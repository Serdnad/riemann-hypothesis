module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle144
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle211
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Bundle010
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen


open MvPolynomial in
private theorem continuous_coeff_blockAct' {Y : Type} [TopologicalSpace Y] {T : Type} {k n : ℕ}
    (A : Y → T → Matrix (Fin k) (Fin k) ℂ) (hA : ∀ t a b, Continuous fun x => A x t a b)
    (F : MvPolynomial (T × Fin k × Fin n) ℂ) :
    ∀ m, Continuous fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (A x) F).coeff m := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x) (C a) = (C a : MvPolynomial (T × Fin k × Fin n) ℂ) :=
      fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x)).commutes a
    simp only [e]
    exact continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add (f := _), AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (hp m).add (hq m)
  | mul_X p w hp =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (A x) (X w) = ∑ b : Fin k, C (A x w.1 w.2.1 b) * X (w.1, (b, w.2.2)) :=
      fun x => aeval_X _ _
    simp only [map_mul, e, Finset.mul_sum, coeff_sum]
    refine continuous_finsetSum _ fun b _ => ?_
    simp only [mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X']
    by_cases hw : ((w.1, (b, w.2.2)) : T × Fin k × Fin n) ∈ m.support
    · simp only [hw, ite_true]
      exact (hA _ _ _).mul (hp _)
    · simp only [hw, ite_false, mul_zero]
      exact continuous_const

private theorem continuous_detTwK' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) :
    Continuous fun x => Formalism.L2.DIV.detTwK lam (g x) := by
  simp only [Formalism.L2.DIV.detTwK]
  refine continuous_finsetProd _ fun τ _ => ?_
  have e : ∀ x, detPow ℂ n (g x τ) (lam τ).detShift =
      ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    intro x
    rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  simp only [e]
  have hc : Continuous fun x => ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_pi fun a => continuous_pi fun b => hg τ a b
  refine hc.matrix_det.zpow₀ _ fun x => Or.inl ?_
  exact (Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit |>.ne_zero


private theorem continuous_rhoK_coeff' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) {d : ℕ} (B : Module.Basis (Fin d) ℂ (Formalism.L2.DIV.VV ℂ lam)) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) (i j : Fin d) :
    Continuous fun x => LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j := by
  classical
  obtain ⟨s, a, ha⟩ := GlobalTheory.IntStruct.exists_coord_eq_sum_coeff (Formalism.L2.DIV.VV ℂ lam) B i
  have e : ∀ x, LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j = ∑ m : s, a m *
      (Formalism.L2.DIV.detTwK lam (g x) * (Formalism.GradedWeylDivisibility.blockAct ℂ
        (fun τ => Matrix.transpose ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        ((B j : Formalism.L2.DIV.VV ℂ lam) : Formalism.L2.DIV.Pol ℂ T n)).coeff m.1) := by
    intro x
    rw [LinearMap.toMatrix_apply, ha]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
  simp only [e]
  exact continuous_finsetSum _ fun m _ => continuous_const.mul ((continuous_detTwK' lam g hg).mul
    (continuous_coeff_blockAct' _ (fun t a b => hg t b a) _ m.1))

private theorem continuous_rep_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a) {d : ℕ}
    (B : Module.Basis (Fin d) ℂ W.Sp) (i j : Fin d) :
    Continuous fun x : infU E a => B.repr (W.rep x (B i)) j := by
  have h := continuous_rhoK_coeff' (T := InfinitePlace E) W B (fun x : infU E a => cAll x.1)
    (fun v p q => GlobalTheory.PolyRealU.continuous_entry v.embedding p q) j i
  refine h.congr fun x => ?_
  rw [LinearMap.toMatrix_apply]
  rfl

theorem UpperTheory.Gal.Gen.wBound_pf :
    UpperTheory.Gal.Gen.WBound := by
  intro E _ _ _ a W d B
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hc : Continuous fun x : infU E a => fun (i j : Fin d) => B.repr (W.rep x (B i)) j :=
    continuous_pi fun i => continuous_pi fun j => continuous_rep_coeff W B i j
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x i j => ?_⟩
  exact ((norm_le_pi_norm (fun j => B.repr (W.rep x (B i)) j) j).trans
    (norm_le_pi_norm (fun (i j : Fin d) => B.repr (W.rep x (B i)) j) i)).trans (hC x (Set.mem_univ _))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    open MvPolynomial in
    have h : ∀ i, ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
        B.repr v i = ∑ m : s, a m * AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 := by
      intro i
      classical
      let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
      let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
      have hR : LinearMap.ker R = ⊥ := by
        refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
        have h0 : ∀ m : s, AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 = 0 := fun m => congrFun hv m
        refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
        by_cases hm : m ∈ s
        · simpa using h0 ⟨m, hm⟩
        · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
            calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
              _ = _ := by rw [Submodule.coe_sum]; rfl
          rw [hv', coeff_sum]
          simp only [MvPolynomial.coeff_smul, ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
          refine Finset.sum_eq_zero fun j _ => ?_
          have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
            hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
          rw [notMem_support_iff.1 this, smul_zero]
      obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
      refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
      have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
        rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
      rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [hs, smul_eq_mul, mul_comm]
      rfl
    choose s a ha using h
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)

      rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i

      rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)

    rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : AddMonoidAlgebra.coeff (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) m =
        (l : ℂ) ^ k * AddMonoidAlgebra.coeff x.1 m := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open Topology Filter

section
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

private lemma strict_pow (N : ℕ) :
    HasStrictFDerivAt (fun x : R => x ^ N) ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) (1 : R) := by
  refine (hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_
  simp only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]
  rw [Nat.cast_smul_eq_nsmul]

private lemma map_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0) :
    map (fun x : R => x ^ N) (𝓝 1) = 𝓝 1 := by
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let e : R ≃L[𝕜] R := ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R)
    ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN'])
    (fun x => by simp [smul_smul, hN'])
  have hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1 := strict_pow (𝕜 := 𝕜) N
  simpa using hf.map_nhds_eq_of_equiv

private lemma units_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0)
    {V : Set Rˣ} (hV : V ∈ 𝓝 (1 : Rˣ)) : (fun x => x ^ N) '' V ∈ 𝓝 (1 : Rˣ) := by
  have he := Units.isOpenEmbedding_val (R := R)
  have h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R) := by
    simpa using he.image_mem_nhds.mpr hV
  have h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R) := by
    rw [← map_pow_nhds (𝕜 := 𝕜) hN]
    exact image_mem_map h1
  rw [← he.image_mem_nhds]
  rw [Set.image_image, Units.val_one]
  rw [Set.image_image] at h2
  simpa using h2
end

theorem UpperTheory.Gal.Gen.powNhds_pf :
    UpperTheory.Gal.Gen.PowNhds := by
  intro E _ _ w a N hN V hV
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E))
      (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))
  exact units_pow_nhds (𝕜 := w.adicCompletion E) hN hV
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

private lemma coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m

  rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

private lemma coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m

  rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

private lemma coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

private lemma coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

private lemma coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private lemma coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

private lemma coefLe_monomial_image {τ : Type} {y : σ → MvPolynomial τ ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ v, CoefLe ι R (y v)) (m : σ →₀ ℕ) :
    CoefLe ι (R ^ (m.sum fun _ e => e)) (m.prod fun v e => y v ^ e) := by
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => R ^ m v)
    (fun _ => pow_nonneg hR _) (fun v _ => coefLe_pow ι hR (hy v) (m v))
  rwa [Finset.prod_pow_eq_pow_sum] at h

end CoefLeLemmas

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.blockBound_pf :
    UpperTheory.Gal.Gen.BlockBound := by
  intro l _ ι T n A R hR hA D x hx h1
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hy : ∀ v, CoefLe ι R (y v) := fun v =>
    coefLe_sum ι _ _ hR0 fun b _ => coefLe_C_mul_X ι hR (hA _ _ _) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (AddMonoidAlgebra.coeff x m) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]

    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : (m.sum fun _ e => e) ≤ D := (MvPolynomial.le_totalDegree hm).trans hx
  calc _ ≤ 1 * R ^ (m.sum fun _ e => e) :=
        mul_le_mul (h1 m) (coefLe_monomial_image ι hR0 hy m k) (norm_nonneg _) zero_le_one
    _ ≤ R ^ D := by
        rw [one_mul]
        exact pow_le_pow_right₀ hR hdeg
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rhoBound_pf :
    UpperTheory.Gal.Gen.DegLe → UpperTheory.Gal.Gen.BlockBound → UpperTheory.Gal.Gen.DetBound → UpperTheory.Gal.Gen.SizeLe → UpperTheory.Gal.Gen.RhoBound := by
  intro hdeg hblk hdet hsize E _ _ _ l _ ι a W A R hR hA x hx m
  have hx' : (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ).totalDegree
      ≤ ∑ τ, ∑ i, (W τ).natW i := hdeg (InfinitePlace E) a W x x.2
  have hb := hblk l ι (InfinitePlace E) a (fun τ => ((A τ : Matrix (Fin a) (Fin a) ℂ)).transpose) R hR
    (fun τ i j => (hA τ j i).1) _ x hx' hx m
  have hd := hdet l ι (InfinitePlace E) a W A R hR hA
  have hs := hsize E a W
  have hcoe : (((Formalism.L2.DIV.rhoK W) A) x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ)
      = Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ) := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  calc ‖ι.symm (Formalism.L2.DIV.detTwK W A)‖ * ‖ι.symm (AddMonoidAlgebra.coeff (Formalism.L2.DIV.trAct A (x : MvPolynomial _ ℂ)) m)‖
      ≤ R ^ (∑ τ, a * (W τ).detShift.natAbs) * R ^ (∑ τ, ∑ i, (W τ).natW i) :=
        mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)
    _ = R ^ (∑ τ, ∑ i, (W τ).natW i + ∑ τ, a * (W τ).detShift.natAbs) := by
        rw [← pow_add, add_comm]
    _ ≤ R ^ (a * GlobalTheory.CongW.wtSize W.at) := pow_le_pow_right₀ hR hs
end
