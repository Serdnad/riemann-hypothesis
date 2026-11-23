module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.PhragmenLindelof
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

noncomputable section
namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_factor (s c : ℂ) :
    ‖2 * (2 * (Real.pi : ℂ)) ^ (-(s + c)) * Complex.Gamma (s + c)‖ =
      2 * (2 * Real.pi) ^ (-(s.re + c.re)) * ‖Complex.Gamma (s + c)‖ := by
  have h2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, norm_mul, h2, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem norm_archFactor_real {I : Type} [Fintype I] (n : I → ℤ) {x : ℝ} (hx : 0 < x) :
    ‖archFactor n (x : ℂ)‖ = ∏ i, (2 * (2 * Real.pi) ^ (-(x + ((|n i| : ℤ) : ℝ) / 2)) *
      Real.Gamma (x + ((|n i| : ℤ) : ℝ) / 2)) := by
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_factor]
  have hc : ((x : ℂ) + ((|n i| : ℤ) : ℂ) / 2) = ((x + ((|n i| : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  rw [hc, Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by linarith))]
  congr 3
  simp

theorem norm_archFactor_le {I : Type} [Fintype I] (n : I → ℤ) {s : ℂ} (hs : 0 < s.re) :
    ‖archFactor n s‖ ≤ ‖archFactor n (s.re : ℂ)‖ := by
  rw [norm_archFactor_real n hs]
  unfold archFactor
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_factor]
  have h0 : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
  have hre : (s + ((|n i| : ℤ) : ℂ) / 2).re = s.re + ((|n i| : ℤ) : ℝ) / 2 := by simp
  have hre' : (((|n i| : ℤ) : ℂ) / 2).re = ((|n i| : ℤ) : ℝ) / 2 := by simp
  rw [hre']
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := PI.EF.norm_Gamma_le (w := s + ((|n i| : ℤ) : ℂ) / 2) (by rw [hre]; linarith)
  rwa [hre] at this

theorem pl_strip {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b C : ℝ} (hab : a < b)
    (hbd : ∃ C' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C')
    (ha : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C) (hb : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  refine PhragmenLindelof.vertical_strip hf.diffContOnCl ?_ ha hb hza hzb
  refine ⟨0, div_pos Real.pi_pos (sub_pos.2 hab), 0, ?_⟩
  obtain ⟨C', hC'⟩ := hbd
  refine Asymptotics.IsBigO.of_bound C' ?_
  refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, norm_one, mul_one]
  exact hC' z hz.1.le hz.2.le

theorem factor_three_halves_le {c : ℝ} (hc : 1 ≤ c) :
    2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c) ≤
      2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (1 + c) * (1 + c) := by
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h1 : (2 * Real.pi) ^ (-(3 / 2 + c)) ≤ (2 * Real.pi) ^ (-(1 + c)) :=
    Real.rpow_le_rpow_of_exponent_le hpi (by linarith)
  have h2 : Real.Gamma (3 / 2 + c) ≤ Real.Gamma (1 + c + 1) :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)
  rw [Real.Gamma_add_one (by linarith)] at h2
  have hg : 0 ≤ Real.Gamma (3 / 2 + c) := (Real.Gamma_pos_of_pos (by linarith)).le
  have hp : 0 ≤ (2 * Real.pi) ^ (-(1 + c)) := by positivity
  calc 2 * (2 * Real.pi) ^ (-(3 / 2 + c)) * Real.Gamma (3 / 2 + c)
      ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * Real.Gamma (3 / 2 + c) := by gcongr
    _ ≤ 2 * (2 * Real.pi) ^ (-(1 + c)) * ((1 + c) * Real.Gamma (1 + c)) := by gcongr
    _ = _ := by ring

theorem archFactor_three_halves_le {I : Type} [Fintype I] (m : I → ℤ) (hm : ∀ i, 0 < m i) :
    ‖archFactor (fun i => 2 * m i) (3 / 2)‖ ≤ ‖archFactor (fun i => 2 * m i) 1‖ * ∏ i, (1 + (m i : ℝ)) := by
  have e32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e1 : (1 : ℂ) = ((1 : ℝ) : ℂ) := by simp
  rw [e32, e1, norm_archFactor_real _ (by norm_num), norm_archFactor_real _ (by norm_num), ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ => ?_) fun i _ => ?_
  · have : 0 < 3 / 2 + ((|2 * m i| : ℤ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((|2 * m i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
    have := Real.Gamma_pos_of_pos this
    positivity
  · have hc : ((|2 * m i| : ℤ) : ℝ) / 2 = (m i : ℝ) := by
      rw [abs_of_pos (by have := hm i; omega)]; push_cast; ring
    rw [hc]
    exact factor_three_halves_le (by exact_mod_cast hm i)

end GlobalTheory.HeckeLOneBound

namespace GlobalTheory.HeckeLOneBound
open GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

theorem norm_heckeL_one_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → IsCMType φ →
    ∀ (χ : HChar E) (m : I → ℤ) (a : HeightOneSpectrum (𝓞 E) →₀ ℕ) (Λ : ℂ → ℂ),
    IsUnitary χ → TrivOnF χ → HasInf χ φ m → (∀ i, 0 < m i) → (∀ v, ExpAt χ v (a v)) → IsHeckeL χ Λ →
    ‖Λ 1‖ ≤ ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E *
      ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℝ)) * ∏ i, (1 + (m i : ℝ)) := by
  intro E _ _ _ I _ φ hFE hB hφ χ m a Λ hu htr hinf hpos ha hL
  set n : I → ℤ := fun i => 2 * m i with hn_def
  set A : ℕ := (discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hA_def
  set Z : ℝ := ‖riemannZeta (3 / 2)‖ ^ Module.finrank ℚ E with hZ_def
  have hinf' : Formalism.L2.Host.HChar.HasInf χ φ n := hinf
  obtain ⟨i₀⟩ := GlobalTheory.LValNe.nonempty_of_isCMType hφ
  have hn : ∃ i, n i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hn' : ∃ i, (fun i => -n i) i ≠ 0 := ⟨i₀, by have := hpos i₀; simp only [hn_def]; omega⟩
  have hu' := GlobalTheory.Published.HeckeFEModel.isUnitary_inv hu
  have hinv := GlobalTheory.Published.HeckeFEModel.hasInf_inv hinf'
  obtain ⟨Λc, hΛc, hbc⟩ := hB E I φ hφ χ n hu hinf' hn
  obtain ⟨Λc', hΛc', -⟩ := hB E I φ hφ χ⁻¹ (fun i => -n i) hu' hinv hn'
  obtain ⟨ε, hε, hfe⟩ := hFE E I φ hφ χ n a Λc Λc' hu hinf' hn ha hΛc hΛc'
  have hL' : IsHeckeL χ⁻¹ Λ := GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ Λ htr hL
  have harch : archFactor (fun i => -n i) = archFactor n := by
    funext s; unfold archFactor; simp only [abs_neg]
  have hApos : 0 < A := by
    refine Nat.mul_pos (Int.natAbs_pos.2 (discr_ne_zero E)) ?_
    unfold Finsupp.prod
    exact Finset.prod_pos fun v _ => pow_pos (Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)) _
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hApos
  have hZ0 : 0 ≤ Z := by positivity
  set F : ℝ := ‖archFactor n (3 / 2)‖ with hF_def
  have hF0 : 0 ≤ F := norm_nonneg _

  have hline : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ F * Z := fun s hs => by
    rw [hΛc.eq_mul hL (by rw [hs]; norm_num), norm_mul]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ Λ s hu hL hs.ge) (norm_nonneg _) hF0
  have hline' : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc' s‖ ≤ F * Z := fun s hs => by
    rw [hΛc'.eq_mul hL' (by rw [hs]; norm_num), norm_mul, harch]
    have h1 := norm_archFactor_le n (s := s) (by rw [hs]; norm_num)
    rw [hs] at h1
    have h1' : ‖archFactor n s‖ ≤ F := by
      rw [hF_def]; convert h1 using 3; push_cast; ring
    exact mul_le_mul h1' (GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow E χ⁻¹ Λ s hu' hL' hs.ge) (norm_nonneg _) hF0

  have hleft : ∀ s : ℂ, s.re = -1 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    rw [hfe s, norm_mul, norm_mul, hε, one_mul, Complex.norm_natCast_cpow_of_pos hApos]
    have hre : (1 / 2 - s).re = 1 := by
      simp only [Complex.sub_re, hs]; norm_num
    rw [hre, Real.rpow_one, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hline' _ ?_) (by positivity)
    simp only [Complex.sub_re, Complex.one_re, hs]; norm_num
  have hright : ∀ s : ℂ, s.re = 3 / 2 → ‖Λc s‖ ≤ A * F * Z := fun s hs => by
    refine (hline s hs).trans ?_
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hA1

  have hbd := hbc (-1 / 2) (3 / 2) (by norm_num)
  have h1 : ‖Λc 1‖ ≤ A * F * Z :=
    pl_strip hΛc.1 (by norm_num) hbd hleft hright (by norm_num) (by norm_num)

  have hg : ∀ i, Complex.Gamma ((1 : ℂ) + ((|n i| : ℤ) : ℂ) / 2) ≠ 0 := fun i => by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    have : (0 : ℝ) ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg (n i)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.intCast_re, Complex.intCast_im]
    norm_num
    positivity
  have e1 := GlobalTheory.LValNe.completed_eq hΛc hL hg
  have hG : 0 < ‖archFactor n 1‖ := norm_pos_iff.2 (GlobalTheory.LValNe.archFactor_ne_zero hg)
  have hrat := archFactor_three_halves_le m hpos
  rw [e1, norm_mul] at h1
  have hP0 : 0 ≤ ∏ i, (1 + (m i : ℝ)) :=
    Finset.prod_nonneg fun i _ => by have : (0 : ℝ) < m i := by exact_mod_cast hpos i
                                     linarith
  have key : ‖archFactor n 1‖ * ‖Λ 1‖ ≤ ‖archFactor n 1‖ * (Z * (A : ℝ) * ∏ i, (1 + (m i : ℝ))) := by
    refine h1.trans ?_
    have : A * F * Z ≤ A * (‖archFactor n 1‖ * ∏ i, (1 + (m i : ℝ))) * Z := by gcongr
    refine this.trans (le_of_eq ?_)
    ring
  exact le_of_mul_le_mul_left key hG

end GlobalTheory.HeckeLOneBound

end
end

section

noncomputable section

namespace GlobalTheory.AdjugateAppendColumn

open Matrix

section General

variable {E : Type} [Field E] (s : E →+* E)

def adj {a b : Type} (A : Matrix a b E) : Matrix b a E := (A.map s)ᵀ

theorem adj_mul {a b c : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b c E) :
    adj s (A * B) = adj s B * adj s A := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adj_one {a : Type} [DecidableEq a] : adj s (1 : Matrix a a E) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem adj_sub {a b : Type} (A B : Matrix a b E) : adj s (A - B) = adj s A - adj s B := by
  ext i j; simp [adj]

theorem adj_smul {a b : Type} (c : E) (A : Matrix a b E) : adj s (c • A) = s c • adj s A := by
  ext i j; simp [adj]

theorem adj_adj (hs : ∀ x, s (s x) = x) {a b : Type} (A : Matrix a b E) : adj s (adj s A) = A := by
  ext i j; simp [adj, hs]

variable {n m : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_left_inv {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) :
    ∃ L : Matrix (Fin m) (Fin n) E, L * X = 1 := by
  have hi : Function.Injective X.mulVec := Matrix.mulVec_injective_iff.2 hX
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' X) (LinearMap.ker_eq_bot.2 hi)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem exists_dual [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0)
    {X : Matrix (Fin n) (Fin m) E} (hX : LinearIndependent E Xᵀ) (h0 : adj s X * J * X = 0) :
    ∃ Y : Matrix (Fin n) (Fin m) E, adj s X * J * Y = 1 ∧ adj s Y * J * X = 1 ∧ adj s Y * J * Y = 0 := by
  obtain ⟨L, hL⟩ := exists_left_inv hX
  have flip : ∀ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 → adj s Z * J * X = 1 := fun Z hZ => by
    have := congrArg (adj s) hZ
    rwa [adj_mul, adj_mul, adj_adj s hs, hJ, adj_one, ← Matrix.mul_assoc] at this
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin n) (Fin m) E, adj s X * J * Z = 1 := ⟨J⁻¹ * adj s L, by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit, ← adj_mul, hL, adj_one]⟩
  obtain ⟨G, hG⟩ : ∃ G, G = adj s Z * J * Z := ⟨_, rfl⟩
  have h1 : adj s X * J * (Z - (2 : E)⁻¹ • (X * G)) = 1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, h0, hZ, Matrix.zero_mul, smul_zero, sub_zero]
  refine ⟨_, h1, flip _ h1, ?_⟩
  have hGG : adj s G = G := by
    rw [hG, adj_mul, adj_mul, adj_adj s hs, hJ, Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc _ X G, flip _ h1, Matrix.one_mul, adj_sub, adj_smul, adj_mul, hGG,
    Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc G, Matrix.mul_assoc G, hZ,
    Matrix.mul_one, ← hG, map_inv₀, map_ofNat, sub_sub, ← add_smul, show (2 : E)⁻¹ + 2⁻¹ = 1 by norm_num, one_smul, sub_self]

theorem gram_apply {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) (i : a) (j : b) :
    (adj s A * J * B) i j = (fun k => s (Aᵀ i k)) ⬝ᵥ J *ᵥ (Bᵀ j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]; rfl

theorem form_symm (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (x y : Fin n → E) :
    s ((fun k => s (x k)) ⬝ᵥ J *ᵥ y) = (fun k => s (y k)) ⬝ᵥ J *ᵥ x := by
  have e : ∀ i j, s (J j i) = J i j := fun i j => congrFun (congrFun hJ i) j

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hs, e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def app (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : Matrix (Fin n) (Fin (m + 1)) E :=
  (Matrix.of (Fin.snoc (α := fun _ => Fin n → E) Xᵀ z))ᵀ

theorem app_transpose (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) :
    (app X z)ᵀ = Fin.snoc (α := fun _ => Fin n → E) Xᵀ z := rfl

theorem app_last (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) : (app X z)ᵀ (Fin.last m) = z :=
  Fin.snoc_last (α := fun _ => Fin n → E) z Xᵀ

theorem app_cast (X : Matrix (Fin n) (Fin m) E) (z : Fin n → E) (i : Fin m) : (app X z)ᵀ i.castSucc = Xᵀ i :=
  Fin.snoc_castSucc (α := fun _ => Fin n → E) z Xᵀ i

theorem exists_ext [CharZero E] (hs : ∀ x, s (s x) = x) (hJ : adj s J = J) (hd : J.det ≠ 0) (k : ℕ) :
    ∀ (m : ℕ) (C : Matrix (Fin n) (Fin m) E), n ≤ m + k → LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      ∃ (m' : ℕ) (hm : m ≤ m') (X Y : Matrix (Fin n) (Fin m') E), adj s X * J * X = 0 ∧ adj s Y * J * Y = 0 ∧
        adj s X * J * Y = 1 ∧ (∀ z : Fin n → E, (adj s X * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
          (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0) ∧ X.submatrix id (Fin.castLE hm) = C := by
  have step : ∀ (m : ℕ) (C Y : Matrix (Fin n) (Fin m) E) (z : Fin n → E), LinearIndependent E Cᵀ → adj s C * J * C = 0 →
      adj s Y * J * C = 1 → (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 → (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z ≠ 0 →
      LinearIndependent E (app C z)ᵀ ∧ adj s (app C z) * J * app C z = 0 := by
    intro m C Y z hC h0 h1 a b c hz
    constructor
    · rw [app_transpose]
      refine linearIndependent_finSnoc.2 ⟨hC, fun hm => hz ?_⟩
      obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hm
      have e : C *ᵥ u = z := by
        rw [← hu]; funext i; simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [← e, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at b
      rw [← e, b, Matrix.mulVec_zero]
    · have a' : ∀ i, (fun k => s (Cᵀ i k)) ⬝ᵥ J *ᵥ z = 0 := fun i => by
        have := congrFun a i
        rw [← Matrix.mulVec_mulVec] at this
        exact this
      ext i j
      rw [gram_apply, Matrix.zero_apply]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rw [app_last]; exact c
        | cast j =>
          rw [app_last, app_cast, ← form_symm s hs hJ, a', map_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last => rw [app_last, app_cast]; exact a' i
        | cast j =>
          rw [app_cast, app_cast, ← gram_apply, h0, Matrix.zero_apply]
  induction k with
  | zero =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    refine ⟨m, le_rfl, C, Y, h0, h3, h1, fun z a b c => ?_, rfl⟩
    by_contra hz
    have := (step m C Y z hC h0 h2 a b c hz).1.fintype_card_le_finrank
    simp at this
    omega
  | succ k ih =>
    intro m C hm hC h0
    obtain ⟨Y, h1, h2, h3⟩ := exists_dual s hs hJ hd hC h0
    by_cases H : ∀ z : Fin n → E, (adj s C * J) *ᵥ z = 0 → (adj s Y * J) *ᵥ z = 0 →
      (fun k => s (z k)) ⬝ᵥ J *ᵥ z = 0 → z = 0
    · exact ⟨m, le_rfl, C, Y, h0, h3, h1, H, rfl⟩
    push Not at H
    obtain ⟨z, a, b, c, hz⟩ := H
    obtain ⟨p, q⟩ := step m C Y z hC h0 h2 a b c hz
    obtain ⟨m', hm', X, Y', x1, x2, x3, x4, x5⟩ := ih (m + 1) (app C z) (by omega) p q
    refine ⟨m', by omega, X, Y', x1, x2, x3, x4, ?_⟩
    ext i j
    have := congrFun (congrFun x5 i) j.castSucc
    have e : app C z i j.castSucc = C i j := congrFun (app_cast C z j) i
    exact this.trans e

end General

theorem exists_wittFrame_initCols (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) (r : ℕ) (C : Matrix (Fin n) (Fin (r + 1)) E)
    (hC : LinearIndependent E (Matrix.transpose C)) (h0 : Formalism.UG.cT (σ : E →+* E) C * J * C = 0) :
    ∃ (m : ℕ) (hm : r < m) (X : Matrix (Fin n) (Fin m) E) (Y : Matrix (Fin n) (Fin m) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y ∧ GlobalTheory.StdPar.initCols X (⟨r, hm⟩ : Fin m) = C := by
  have hs : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have := h.2.2.2 τ
    simp only [RingHom.coe_coe]
    rw [this, this, star_star]
  obtain ⟨m, hm, X, Y, x1, x2, x3, x4, x5⟩ := exists_ext (σ : E →+* E) (J := J) hs (Matrix.ext fun i j => hJ.1 i j) hJ.2
    n (r + 1) C (by omega) hC h0
  refine ⟨m, hm, X, Y, ⟨x1, x2, x3, fun z a b c => x4 z a b ?_⟩, x5⟩
  simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE, Formalism.UG.hform] at c
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using c

end GlobalTheory.AdjugateAppendColumn

end
end

section

open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.StdPar
open scoped TensorProduct

namespace GlobalTheory.ColumnSpanCoefficients

theorem exists_coeff_of_mem_colSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n r s : ℕ} (hs : s ≤ r) (X : Matrix (Fin n) (Fin r) E) (I : Set (Fin r)) (P : Fin s → Prop)
    (hI : ∀ i ∈ I, ∃ j : Fin s, Fin.castLE hs j = i ∧ P j) {y : Fin n → AF F ⊗[F] E} (hy : y ∈ colSpan F X I) :
    ∃ a : Fin s → AF F ⊗[F] E, (∀ j, ¬ P j → a j = 0) ∧ adMat F (X.submatrix id (Fin.castLE hs)) *ᵥ a = y := by
  classical
  rw [colSpan] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨j, rfl, hj⟩ := hI i hi
    refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
    · rw [Pi.single_apply, if_neg]
      rintro rfl
      exact hj' hj
    · rw [Matrix.mulVec_single_one]
      ext r
      rfl
  | zero => exact ⟨0, fun _ _ => rfl, Matrix.mulVec_zero _⟩
  | add x z _ _ hx hz =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hz
    exact ⟨a + b, fun j hj => by simp [ha j hj, hb j hj], Matrix.mulVec_add _ _ _⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨c • a, fun j hj => by simp [ha j hj], Matrix.mulVec_smul _ _ _⟩

end GlobalTheory.ColumnSpanCoefficients
end

section

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z



end GlobalTheory.IdTorus
end
end

section

open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.cm_galois_representation_crystalline : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.HeckeLAdicCharacter →
  GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
    ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
    ∀ (f : ℂ) (J : (E →+* Qbar l) → Multiset ℤ),
      (∀ τ, (J τ).map (fun k : ℤ => (k : ℂ)) = (m (ι.toRingHom.comp τ)).map (fun z => f - z)) →
    ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧
      ((∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → ∃ σ : SmIrr (GL (Fin a) (w.adicCompletion E)),
          P.IsLocComp w σ ∧ GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a))) → GlobalTheory.ExpFrame.CrysWith r J) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
        ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), P.IsLocComp w σ → ∀ S : Multiset ℂˣ,
          GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ (B : ValuationSubring Ω) (g : G E Ω), IsPlaceOver (F := E) B w →
            IsFrob (F := E) B (normV w) g →
            (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
              Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ f))).prod := by
  first | exact @GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | exact GlobalTheory.CsdTwistGal.exists_galRep_csd_twist | (intros; apply GlobalTheory.CsdTwistGal.exists_galRep_csd_twist <;> assumption)
end
