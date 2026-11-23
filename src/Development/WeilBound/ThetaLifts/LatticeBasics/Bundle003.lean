module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
public import GroundTheory.AutomorphicForms.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TendstoPrimeIdealZetaSumUniv
public import Mathlib.NumberTheory.NumberField.DirichletDensity

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexOrder Kronecker

variable {n d : ℕ}

def hf (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  trace (xᵀ * A * y.map star * Cᵀ)

def cs (θ : Matrix (Fin n) (Fin n) ℂ) (θ' : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin d) ℂ where
  toFun x := Complex.I • (θ * x * θ'ᵀ)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' t x := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
    rw [smul_comm]

theorem map_star_mul {a b c : ℕ} (x : Matrix (Fin a) (Fin b) ℂ) (y : Matrix (Fin b) (Fin c) ℂ) :
    (x * y).map star = x.map star * y.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, star_sum, star_mul']

private theorem map_star_smul_matrix {a b : ℕ} (c : ℂ) (M : Matrix (Fin a) (Fin b) ℂ) :
    (c • M).map star = star c • M.map star := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul']

theorem star_cs (θ : Matrix (Fin n) (Fin n) ℂ) (θ' : Matrix (Fin d) (Fin d) ℂ) (x) :
    (cs θ θ' x).map star = (-Complex.I) • (θ.map star * x.map star * (θ'.map star)ᵀ) := by
  rw [show cs θ θ' x = Complex.I • (θ * x * θ'ᵀ) from rfl, map_star_smul_matrix, map_star_mul, map_star_mul,
    Matrix.transpose_map, show star Complex.I = -Complex.I from Complex.conj_I]

theorem posDef_cartan {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) : (M * θ.map star).PosDef := by
  obtain ⟨h1, h2, h3⟩ := h
  have hbar : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1, Matrix.map_one _ (by simp) (by simp)]
  have hcomm : θᵀ * M = M * θ.map star := by
    calc θᵀ * M = θᵀ * M * (θ.map star * θ.map star) := by rw [hbar, Matrix.mul_one]
      _ = (θᵀ * M * θ.map star) * θ.map star := by simp only [Matrix.mul_assoc]
      _ = M * θ.map star := by rw [h2]
  have hH : (M * θ.map star).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hM, ← hcomm]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hy : θ *ᵥ star x ≠ 0 := by
    intro h0
    apply hx
    have h5 : θ *ᵥ (θ *ᵥ star x) = 0 := by rw [h0, Matrix.mulVec_zero]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h5
    simpa using h5
  have hs : star (θ *ᵥ star x) = θ.map star *ᵥ x := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, star_mul']
  have heq : (θ *ᵥ (θ *ᵥ star x)) ⬝ᵥ M *ᵥ star (θ *ᵥ star x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, hs, Matrix.mulVec_mulVec]
  have hpos := h3 _ hy
  rw [Complex.pos_iff]
  refine ⟨by rw [← heq]; exact hpos, ?_⟩
  have him := hH.im_star_dotProduct_mulVec_self x
  simp only [RCLike.im_to_complex] at him
  exact him.symm

variable {A θ : Matrix (Fin n) (Fin n) ℂ} {C θ' : Matrix (Fin d) (Fin d) ℂ}

theorem hf_cs_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x y) :
    hf A C (cs θ θ' x) (cs θ θ' y) = hf A C x y := by
  have e : θ'ᵀ * C * θ'.map star = C := by
    have := h'.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have e' : (θ'.map star)ᵀ * Cᵀ * θ' = Cᵀ := by
    simpa only [transpose_mul, transpose_transpose, Matrix.mul_assoc] using congrArg transpose e
  rw [hf, star_cs, hf]
  simp only [cs, LinearMap.coe_mk, AddHom.coe_mk, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul,
    transpose_mul, transpose_transpose]
  rw [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  conv_rhs => rw [← h.2.1, ← e']
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem cs_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x) : cs θ θ' (cs θ θ' x) = -x := by
  show Complex.I • (θ * (Complex.I • (θ * x * θ'ᵀ)) * θ'ᵀ) = -x
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I]
  have e1 : θ * (θ * x * θ'ᵀ) * θ'ᵀ = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, h'.1, Matrix.transpose_one, Matrix.mul_one]
  rw [e1, neg_one_smul]

private theorem hf_neg_right_lattice_basics (u v : Matrix (Fin n) (Fin d) ℂ) : hf A C u (-v) = -hf A C u v := by
  unfold hf
  rw [Matrix.map_neg _ star_neg, Matrix.mul_neg, Matrix.neg_mul, Matrix.trace_neg]

theorem hf_cs (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ') (x y) :
    hf A C (cs θ θ' x) y = -hf A C x (cs θ θ' y) := by
  calc hf A C (cs θ θ' x) y = hf A C (cs θ θ' x) (cs θ θ' (cs θ θ' (-y))) := by rw [cs_cs h h', neg_neg]
    _ = hf A C x (cs θ θ' (-y)) := hf_cs_cs h h' x _
    _ = -hf A C x (cs θ θ' y) := by rw [map_neg, hf_neg_right_lattice_basics]

private theorem trace_transpose_mul_eq_star_dotProduct (x W : Matrix (Fin n) (Fin d) ℂ) :
    trace (xᵀ * W) = star (fun p : Fin n × Fin d => x.map star p.1 p.2) ⬝ᵥ (fun p => W p.1 p.2) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
    Fintype.sum_prod_type, Pi.star_apply, Matrix.map_apply, star_star]
  exact Finset.sum_comm

private theorem kroneckerMap_mul_mulVec_eq_mul_mul_transpose (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ)
    (Z : Matrix (Fin n) (Fin d) ℂ) :
    Matrix.kroneckerMap (fun a b => a * b) P Q *ᵥ (fun p : Fin n × Fin d => Z p.1 p.2) =
      fun p => (P * Z * Qᵀ) p.1 p.2 := by
  funext p
  obtain ⟨i, a⟩ := p
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_neg (hA : Aᴴ = A) (hC : (Complex.I • C)ᴴ = Complex.I • C) (h : IsCartan A θ) (h' : IsCartan (Complex.I • C) θ')
    {x : Matrix (Fin n) (Fin d) ℂ} (hx : x ≠ 0) : (hf A C x (cs θ θ' x)).re < 0 := by
  have hK := (posDef_cartan hA h).kronecker (posDef_cartan hC h')
  have key1 : hf A C x (cs θ θ' x) =
      -trace (xᵀ * (A * θ.map star * x.map star * (Complex.I • C * θ'.map star)ᵀ)) := by
    unfold hf
    rw [star_cs]
    simp only [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.mul_assoc, neg_smul, Matrix.trace_neg, Matrix.mul_neg, Matrix.neg_mul]
  have hz : (fun p : Fin n × Fin d => x.map star p.1 p.2) ≠ 0 := by
    intro h0
    apply hx
    ext i a
    have := congrFun h0 (i, a)
    simpa using this
  have hpos := hK.re_dotProduct_pos hz
  rw [key1, trace_transpose_mul_eq_star_dotProduct, ← kroneckerMap_mul_mulVec_eq_mul_mul_transpose (A * θ.map star) (Complex.I • C * θ'.map star) (x.map star)]
  simp only [RCLike.re_to_complex] at hpos
  rw [Complex.neg_re]
  linarith

end GlobalTheory.ThK.Dbl.Dense

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Host (HChar)
open GlobalTheory.CMVal (eulerFactor)
open Neutral.B1 (Ideles diagUnits localIdele)
open ReciprocityTheory.Neutral.Bridge

variable {K : Type} [Field K] [NumberField K]

theorem exp_neg_le_norm_inv {z : ℂ} {x : ℝ} (hx : x < 1) (hz : ‖z‖ = x) : Real.exp (-x) ≤ ‖(1 - z)⁻¹‖ := by
  have h0 : 0 < ‖1 - z‖ := lt_of_lt_of_le (by rw [norm_one, hz]; linarith) (norm_sub_norm_le 1 z)
  rw [norm_inv, Real.exp_neg]
  refine inv_anti₀ h0 ((norm_sub_le _ _).trans ?_)
  rw [norm_one, hz, add_comm]
  exact Real.add_one_le_exp x

theorem exp_le_inv {x : ℝ} (hx : x < 1) : Real.exp x ≤ ‖(1 - (x : ℂ))⁻¹‖ := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith),
    le_inv_comm₀ (Real.exp_pos x) (by linarith), ← Real.exp_neg]
  linarith [Real.add_one_le_exp (-x)]

theorem hchar_eq_one (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (χ : HChar K) (hu : χ.IsUnitary)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (h : ∀ w ∉ S, (Ideal.absNorm w.asIdeal).Prime → ∀ x, χ.loc w x = 1) : χ = 1 := by
  classical
  by_contra hne
  obtain ⟨Λ, ⟨hA, hP⟩, -⟩ := (H K χ hu).2 hne
  obtain ⟨C, hC⟩ := exists_bound_primeIdealZetaSum_not_prime (K := K)
  set A : Set (HeightOneSpectrum (𝓞 K)) := {w | ¬ (Ideal.absNorm w.asIdeal).Prime}
  have key : ∀ s : ℝ, 1 < s → Real.exp (NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s -
      2 * (C + hS.toFinset.card)) ≤ ‖Λ s‖ := fun s hs => by
    set x : HeightOneSpectrum (𝓞 K) → ℝ := fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) with hx
    have x0 : ∀ w, 0 ≤ x w := fun w => by positivity
    have x1 : ∀ w, x w < 1 := fun w =>
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith [DedekindZetaReal.two_le_absNorm K w]) (by linarith)
    have xc : ∀ w : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)) = x w := fun w => by
      rw [hx, Complex.ofReal_cpow (Nat.cast_nonneg _)]; simp
    have sx : Summable x := summable_absNorm_rpow K hs
    have s1 : HasSum (fun w => x w - 2 * (A.indicator x w + (hS.toFinset : Set _).indicator x w))
        (∑' w, x w - 2 * (∑' w : A, x w + ∑ w ∈ hS.toFinset, x w)) :=
      sx.hasSum.sub (((hasSum_subtype_iff_indicator.1 (sx.subtype (· ∈ A)).hasSum).add
        (hasSum_subtype_iff_indicator.1 (hS.toFinset.hasSum x))).mul_left 2)
    have le : ∀ w, Real.exp (x w - 2 * (A.indicator x w + (hS.toFinset : Set _).indicator x w)) ≤ ‖eulerFactor χ s w‖ := fun w => by
      by_cases hw : w ∈ A ∨ w ∈ (hS.toFinset : Set _)
      · have a1 := Set.indicator_nonneg (s := A) (fun v _ => x0 v) w
        have a2 := Set.indicator_nonneg (s := (hS.toFinset : Set _)) (fun v _ => x0 v) w
        refine le_trans (b := Real.exp (-x w)) (Real.exp_le_exp.2 ?_) ?_
        · rcases hw with hw | hw <;> rw [Set.indicator_of_mem hw] at * <;> linarith
        · unfold eulerFactor
          split_ifs
          · exact exp_neg_le_norm_inv (x1 w) (by
              rw [norm_mul, xc, Complex.norm_real, Real.norm_of_nonneg (x0 w)]
              exact (congrArg (· * x w) (hu _)).trans (one_mul _))
          · rw [norm_one]; exact Real.exp_le_one_iff.2 (by linarith [x0 w])
      · push Not at hw
        have hl := h w (by simpa using hw.2) (not_not.1 hw.1)
        rw [Set.indicator_of_notMem hw.1, Set.indicator_of_notMem hw.2, eulerFactor, if_pos (show χ.UnrAt w from fun y _ => hl y),
          show χ.val w = 1 from hl _, xc]
        simpa using exp_le_inv (x1 w)
    refine le_trans (Real.exp_le_exp.2 ?_) (le_of_tendsto_of_tendsto' s1.rexp (hP s hs).norm fun T =>
      Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun w _ => le w)
    have e1 : ∑' w : A, x w ≤ C := by
      simpa only [NumberField.Set.primeIdealZetaSum_def, hx] using hC s hs
    have e2 : ∑ w ∈ hS.toFinset, x w ≤ hS.toFinset.card := by
      simpa using Finset.sum_le_card_nsmul _ _ 1 fun w _ => (x1 w).le
    rw [NumberField.Set.primeIdealZetaSum_def, tsum_univ x]
    linarith
  have hc : Tendsto (fun s : ℝ => ‖Λ s‖) (𝓝[>] 1) (𝓝 ‖Λ 1‖) :=
    (hA.continuousAt.tendsto.comp ((Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds)).norm
  refine not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp
    (tendsto_atTop_add_const_right _ (-(2 * (C + hS.toFinset.card))) (tendsto_primeIdealZetaSum_univ K)))) _ hc
  filter_upwards [self_mem_nhdsWithin] with s hs using key s hs

theorem exists_prime_norm (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∃ w ∉ S, (Ideal.absNorm w.asIdeal).Prime := by
  by_contra hn
  push Not at hn
  obtain ⟨t, ht⟩ := GlobalTheory.HeckeOne.exists_normChar_ne_one (K := K)
  exact ht (hchar_eq_one H _ (GlobalTheory.HeckeOne.isUnitary_normChar t) hS fun w h1 h2 => absurd h2 (hn w h1))

theorem closed_eq_top [_root_.NumberField.IsTotallyComplex K] (H : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne) (M : Subgroup (Ideles K))
    (hM : IsClosed (M : Set (Ideles K))) (h1 : ∀ k, diagUnits K k ∈ M) (h2 : GlobalTheory.IdeleCovolume.eIdele K ∈ M)
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    (h : ∀ w ∉ S, (Ideal.absNorm w.asIdeal).Prime → ∀ x, localIdele K w x ∈ M) (z : Ideles K) : z ∈ M := by
  obtain ⟨C, hC, hc⟩ := GlobalTheory.IdeleCovolume.exists_compact_idele K
  have : CompactSpace (Ideles K ⧸ M) := ⟨by
    refine (hC.image (QuotientGroup.continuous_mk (N := M))).of_isClosed_subset isClosed_univ fun q _ => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, n, hk⟩ := hc y
    exact ⟨_, hk, by
      rw [mul_comm]; exact QuotientGroup.mk_mul_of_mem y (mul_mem (h1 k) (zpow_mem h2 n))⟩⟩
  by_contra hz
  obtain ⟨χ, hχ⟩ := GroundTheory.Automorphic.CompactAbelianFourier.exists_char_ne_one (C := Ideles K ⧸ M) (g := z)
    fun e => hz ((QuotientGroup.eq_one_iff z).1 e)
  let c : Ideles K →* Circle := χ.toMonoidHom.comp (QuotientGroup.mk' M)
  have cc : Continuous c := χ.continuous.comp QuotientGroup.continuous_mk
  have c1 : ∀ y ∈ M, Circle.toUnits (c y) = 1 := fun y hy => by
    rw [show c y = χ (y : Ideles K ⧸ M) from rfl, (QuotientGroup.eq_one_iff y).2 hy, map_one, map_one]
  let X : HChar K := ⟨Circle.toUnits.comp c, Units.continuous_iff.2 ⟨continuous_subtype_val.comp cc,
    (continuous_subtype_val.comp cc.inv).congr fun x => Circle.coe_inv (c x)⟩, fun k => c1 _ (h1 k)⟩
  have := hchar_eq_one H X (fun x => Circle.norm_coe (c x)) hS fun w a b x => c1 _ (h w a b x)
  exact hχ (Circle.ext (congrArg (fun Y : HChar K => ((Y.1 z : ℂˣ) : ℂ)) this))

end GlobalTheory.ThK.Dbl

end
end
