module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PCkPartials
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle086
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle050
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.ChainRuleFormalGroupVar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle003

@[expose] public section

section

open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCrit

open GlobalTheory.UnitarySmVec GlobalTheory.HolDict

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem contDiff_expM : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_init {k : ℕ} : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.init t :=
  contDiff_pi.2 fun j => contDiff_apply ℝ (fun _ => ℝ) (Fin.castSucc j)

theorem contDiff_pr : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ (pr Xs)
  | 0, Xs => by
    have e : pr Xs = fun _ => 1 := funext (pr_zero Xs)
    rw [e]
    exact contDiff_const
  | k + 1, Xs => by
    have e : pr Xs = fun t => pr (Fin.init Xs) (Fin.init t) * NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)) :=
      funext (pr_succ Xs)
    rw [e]
    exact ((contDiff_pr (Fin.init Xs)).comp contDiff_init).mul
      (contDiff_expM.comp ((contDiff_apply ℝ (fun _ => ℝ) (Fin.last k)).smul contDiff_const))

theorem coord {Hm : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit Hm.det) : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    (∀ j, Xs j ∈ lieH Hm) → ∀ m : Fin k, ∃ Y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ, ContDiff ℝ ∞ Y ∧
      (∀ t, Y t ∈ lieH Hm) ∧
      ∀ (t : Fin k → ℝ) (s : ℝ), pr Xs (t + s • Pi.single m 1) = pr Xs t * NormedSpace.exp (s • Y t) := by
  intro k
  induction k with
  | zero => exact fun _ _ m => m.elim0
  | succ k ih =>
    intro Xs hX m
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · refine ⟨fun _ => Xs (Fin.last k), contDiff_const, fun _ => hX _, fun t s => ?_⟩
      have e1 : Fin.init (t + s • Pi.single (Fin.last k) (1:ℝ)) = Fin.init t := by
        funext j
        simp [Fin.init, Fin.castSucc_ne_last]
      have e2 : (t + s • Pi.single (Fin.last k) (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) + s := by simp
      rw [pr_succ, pr_succ Xs t, e1, e2, add_smul,
        Matrix.exp_add_of_commute _ _ (((Commute.refl (Xs (Fin.last k))).smul_left _).smul_right _), mul_assoc]
    · obtain ⟨Y', hY', hYl, hYe⟩ := ih (Fin.init Xs) (fun j => hX (Fin.castSucc j)) m'
      refine ⟨fun t => NormedSpace.exp (-(t (Fin.last k) • Xs (Fin.last k))) * Y' (Fin.init t) *
        NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)), ?_, ?_, ?_⟩
      · have hl : ContDiff ℝ ∞ fun t : Fin (k+1) → ℝ => t (Fin.last k) • Xs (Fin.last k) :=
          (contDiff_apply ℝ (fun _ => ℝ) (Fin.last k)).smul contDiff_const
        exact ((contDiff_expM.comp hl.neg).mul (hY'.comp contDiff_init)).mul (contDiff_expM.comp hl)
      · intro t
        have hg := exp_mem hu (hX (Fin.last k)) (t (Fin.last k))
        have := lie_conj hu (hYl (Fin.init t)) hg
        simpa only [Matrix.exp_neg] using this
      · intro t s
        have e1 : Fin.init (t + s • Pi.single (Fin.castSucc m') (1:ℝ)) = Fin.init t + s • Pi.single m' 1 := by
          funext j
          simp [Fin.init, Pi.single_apply]
        have e2 : (t + s • Pi.single (Fin.castSucc m') (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) := by
          simp [(Fin.castSucc_lt_last m').ne']
        rw [pr_succ, pr_succ Xs t, e1, e2, hYe]
        beta_reduce
        rw [Matrix.exp_neg]
        have hgd : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))).det :=
          det_unit hu (exp_mem hu (hX (Fin.last k)) (t (Fin.last k)))
        have hgu : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))) := (isUnit_iff_isUnit_det _).2 hgd
        set g := NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))
        rw [show s • (g⁻¹ * Y' (Fin.init t) * g) = g⁻¹ * (s • Y' (Fin.init t)) * g by
            rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' _ _ hgu, mul_assoc, mul_assoc, mul_assoc,
          ← mul_assoc g, mul_nonsing_inv _ hgd, one_mul]

end Mat

section Main
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : Type} {v : ι → H} {δ : Matrix (Fin n) (Fin n) ℂ → ι → ι}

theorem v_zero (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (i : ι) : v (δ 0 i) = 0 := by
  simpa using hs i 0 0

theorem v_sum (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) {β : Type} (s : Finset β)
    (f : β → Matrix (Fin n) (Fin n) ℂ) (i : ι) : v (δ (∑ b ∈ s, f b) i) = ∑ b ∈ s, v (δ (f b) i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using v_zero hs i
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ha, ih]

theorem v_expand (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (Y : Matrix (Fin n) (Fin n) ℂ) (i : ι) :
    v (δ Y i) = ∑ a, ∑ c, (((Y a c).re : ℂ) • v (δ (single a c 1) i) +
      ((Y a c).im : ℂ) • v (δ (Complex.I • single a c 1) i)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : single a c (Y a c) = ((Y a c).re : ℂ) • single a c 1 + ((Y a c).im : ℂ) • (Complex.I • single a c 1) := by
    rw [smul_smul, ← add_smul, Matrix.smul_single, smul_eq_mul, mul_one, Complex.re_add_im]
  rw [e, ha, hs, hs]

theorem crit_nat (hu : IsUnit Hm.det) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ)
    (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i))
    (hd : ∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0)
    {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ j, Xs j ∈ lieH Hm) (N : ℕ) :
    ∀ i, ContDiff ℝ N fun t => σ (pr Xs t) (v i) := by
  choose Y hY hYl hYe using coord hu Xs hX
  induction N with
  | zero =>
    intro i
    simp only [Nat.cast_zero, contDiff_zero]
    exact (hσ.2.2 (v i)).comp_continuous (contDiff_pr Xs).continuous fun t => pr_mem hu Xs hX t
  | succ N ih =>
    intro i
    let D : Fin k → (Fin k → ℝ) → H := fun m t => ∑ a, ∑ c,
      ((Y m t a c).re • σ (pr Xs t) (v (δ (single a c 1) i)) +
        (Y m t a c).im • σ (pr Xs t) (v (δ (Complex.I • single a c 1) i)))
    have hD : ∀ m, ContDiff ℝ N (D m) := by
      intro m
      have he : ∀ a c, ContDiff ℝ ∞ fun t => Y m t a c := fun a c =>
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)).contDiff.comp (hY m)
      refine ContDiff.sum fun a _ => ContDiff.sum fun c _ => ?_
      exact ((contDiff_infty.1 (Complex.reCLM.contDiff.comp (he a c)) N).smul (ih _)).add
        ((contDiff_infty.1 (Complex.imCLM.contDiff.comp (he a c)) N).smul (ih _))
    have hpart : ∀ y m, HasDerivAt (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) (D m y) 0 := by
      intro y m
      have e : (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) =
          fun s => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)) := by
        funext s
        rw [hYe, hσ.1.2 _ (pr_mem hu Xs hX y) _ (exp_mem hu (hYl m y) s)]
        rfl
      rw [e]
      have h1 : HasDerivAt (fun s : ℝ => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)))
          (σ (pr Xs y) (v (δ (Y m y) i))) 0 :=
        ((σ (pr Xs y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd _ (hYl m y) i)
      convert h1 using 1
      show _ = σ (pr Xs y) (v (δ (Y m y) i))

      rw [v_expand ha hs (Y m y) i, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_

      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_add (f := _), map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun y => ∑ m, (ContinuousLinearMap.proj m : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D m y), ?_, fun y => ?_⟩
    · exact ContDiff.sum fun m _ => contDiff_const.smulRight (hD m)
    · exact PI.UnitaryGroupMassFormula.JCC.Ck.partials_continuous_differentiable k H Set.univ _ D isOpen_univ (fun m => (hD m).continuous.continuousOn)
        (fun y _ m => hpart y m) y trivial

end Main

theorem smoothVec_of_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  intro n Hm H _ _ σ ι v δ hdet hσ ha hs hd i k Xs hX
  have hu : IsUnit Hm.det := isUnit_iff_ne_zero.2 hdet
  exact contDiff_infty.2 fun N => crit_nat hu hσ ha hs hd Xs hX N i

end GlobalTheory.SmoothCrit
end
end

section

open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

noncomputable section
namespace GlobalTheory.HondaCM3

theorem shortW_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K) :
    (Formalism.L2.Th1.A.shortW g2 g3).map φ = Formalism.L2.Th1.A.shortW (φ g2) (φ g3) := by
  ext <;> simp [Formalism.L2.Th1.A.shortW, map_div₀, map_neg, map_ofNat]

theorem ltLog_map {K L : Type} [Field K] [Field L] (φ : K →+* L) (l : ℕ) :
    PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  simp only [coeff_map, ltLog, coeff_mk]
  split_ifs <;> simp [map_inv₀, map_pow, map_natCast]

theorem constantCoeff_ltLog {K : Type} [Field K] (l : ℕ) (hl : 2 ≤ l) :
    constantCoeff (ltLog K l) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, ltLog, coeff_mk, dite_eq_right]
  rintro ⟨j, hj⟩
  have : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  omega

theorem map_subst_of {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f s : K⟦X⟧)
    (hs : constantCoeff s = 0) :
    PowerSeries.map φ (f.subst s) = (PowerSeries.map φ f).subst (PowerSeries.map φ s) :=
  Formalism.L2.Th1.A.More.map_subst' φ (HasSubst.of_constantCoeff_zero hs) f

theorem norm_natCast_eq_one {K : Type} [NormedField K] [IsUltrametricDist K] (l n : ℕ)
    (hl : ‖(l : K)‖ < 1) (hcop : Nat.Coprime n l) : ‖(n : K)‖ = 1 := by
  have hb := Nat.gcd_eq_gcd_ab n l
  rw [hcop] at hb
  have h1 : (1 : K) = (n : K) * (n.gcdA l : K) + (l : K) * (n.gcdB l : K) := by
    have := congrArg (fun z : ℤ => (z : K)) hb
    push_cast at this
    exact this
  have hle : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  refine le_antisymm hle ?_
  by_contra hlt
  push_neg at hlt
  have ha : ‖(n.gcdA l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have hb' : ‖(n.gcdB l : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K _
  have e1 : ‖(n : K) * (n.gcdA l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) ha) hlt
  have e2 : ‖(l : K) * (n.gcdB l : K)‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hb') hl
  have := IsUltrametricDist.norm_add_le_max ((n : K) * (n.gcdA l : K)) ((l : K) * (n.gcdB l : K))
  rw [← h1, norm_one] at this
  exact absurd this (not_le.2 (max_lt e1 e2))

end GlobalTheory.HondaCM3

namespace GlobalTheory.HondaCM3

theorem one_sub_two_omega_sq (d : ℕ) : (1 - 2 * omegaK d) ^ 2 = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  rw [omegaK]
  have : (1 : ℂ) - 2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) = -(Complex.I * ((Real.sqrt d : ℝ) : ℂ)) := by
    ring
  rw [this, neg_sq, mul_pow, Complex.I_sq, h]; ring

theorem cm3 : CM3 := by
  intro d L hsq hd hCM l _ hl5 hld hinert ι g2 g3 hG
  have hG' := hG
  obtain ⟨hg2K, hg3K, hg2n, hg3n, hdisc, lam, hlam0, hg2, hg3⟩ := hG
  haveI : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hl2 : 2 < l := by omega
  obtain ⟨σ, hσ, -⟩ := Formalism.L2.Th1.D.kurFrob l hl2
  obtain ⟨hRes, hUnr⟩ := GlobalTheory.T.maxUnramified_residueAlgClosed_and_frobeniusLift l hl2
  have hU := hUnr σ hσ
  set φ : MaximalUnramifiedExtension l →+* ℂ_[l] := (MaximalUnramifiedExtension l).subtype with hφ
  have hnφ : ∀ x : MaximalUnramifiedExtension l, ‖φ x‖ = ‖x‖ := fun x => rfl
  set a2 : MaximalUnramifiedExtension l := ⟨g2, hg2K⟩ with ha2
  set a3 : MaximalUnramifiedExtension l := ⟨g3, hg3K⟩ with ha3
  have hφa2 : φ a2 = g2 := rfl
  have hφa3 : φ a3 = g3 := rfl
  set f := Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW a2 a3) with hf
  set e := Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW a2 a3) with he
  have hZ := Formalism.L2.Th1.A.zMap (MaximalUnramifiedExtension l) ℂ_[l] φ (Formalism.L2.Th1.A.shortW a2 a3)
  rw [shortW_map, hφa2, hφa3] at hZ
  have hmf : PowerSeries.map φ f = Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3) := hZ.1
  have hme : PowerSeries.map φ e = uSer g2 g3 := by
    rw [hZ.2.1, Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3]
  have hf0 : constantCoeff f = 0 := (Formalism.L2.Th1.A.logSpec (MaximalUnramifiedExtension l) _).1

  have hlK : ‖(l : MaximalUnramifiedExtension l)‖ < 1 := hU.2.2.1
  have h2 : ‖(2 : MaximalUnramifiedExtension l)‖ = 1 := by
    have := norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l 2 hlK
      ((Nat.coprime_primes Nat.prime_two (Fact.out)).2 (by omega))
    simpa using this
  have hInt : IntLog f e := GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass (MaximalUnramifiedExtension l) a2 a3 h2 hg2n hg3n

  obtain ⟨hωK, hσω⟩ := Formalism.L2.Th1.D.sqrtKur d hsq hd l hl5 hinert ι
  set w : MaximalUnramifiedExtension l := ⟨ι (omegaK d), hωK⟩ with hw
  have hσw : σ w = 1 - w := hσω σ hσ w rfl
  have hσσ : σ (σ w) = w := by rw [hσw, map_sub, map_one, hσw]; ring
  have hsq' : (1 - 2 * w) ^ 2 = -((d : ℕ) : MaximalUnramifiedExtension l) := by
    apply (MaximalUnramifiedExtension l).subtype_injective
    have := congrArg ι (one_sub_two_omega_sq d)
    simp only [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast] at this
    rw [map_pow, map_sub, map_one, map_mul, map_ofNat, map_neg, map_natCast]
    exact this
  have hd1 : ‖((d : ℕ) : MaximalUnramifiedExtension l)‖ = 1 :=
    norm_natCast_eq_one (K := MaximalUnramifiedExtension l) l d hlK
      ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hld)))
  have hnorm : ‖σ w - w‖ = 1 := by
    have e1 : σ w - w = 1 - 2 * w := by rw [hσw]; ring
    rw [e1]
    have : ‖1 - 2 * w‖ ^ 2 = 1 := by rw [← norm_pow, hsq', norm_neg, hd1]
    nlinarith [norm_nonneg (1 - 2 * w), sq_nonneg (‖1 - 2 * w‖ - 1)]

  have hCf : ∀ a : MaximalUnramifiedExtension l, constantCoeff (C a * f) = 0 := fun a => by
    rw [map_mul, hf0, mul_zero]
  have hmapMul : ∀ a : MaximalUnramifiedExtension l, PowerSeries.map φ (Formalism.L2.Th1.C.mulBy f e a) =
      Formalism.L2.Th1.C.mulBy (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (uSer g2 g3) (φ a) := by
    intro a
    rw [Formalism.L2.Th1.C.mulBy, Formalism.L2.Th1.C.mulBy, map_subst_of φ e _ (hCf a), hme, map_mul, map_C, hmf]
  have hCoef : CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) := by
    intro n
    have := GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof d L hd hCM l hl5 hld hinert ι g2 g3 hG' n
    rw [← hnφ, ← coeff_map, hmapMul]
    exact this

  have hht : ∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : MaximalUnramifiedExtension l))‖ = 1 := by
    have hc : ι.symm lam ≠ 0 := by simpa using hlam0
    obtain ⟨L', -, hL2, hL3, -, -⟩ := GlobalTheory.T.exists_homothetic_periodPair_lattice L (ι.symm lam) hc
    have e2 : ι L'.g₂ = g2 := by rw [hL2, map_mul, map_pow, RingEquiv.apply_symm_apply, hg2]
    have e3 : ι L'.g₃ = g3 := by rw [hL3, map_mul, map_pow, RingEquiv.apply_symm_apply, hg3]
    obtain ⟨n, hn, h1⟩ := GlobalTheory.T.formalGroup_height_le_two_good_reduction L' l hl5 ι (by rw [e2]; exact hg2n) (by rw [e3]; exact hg3n)
      (by rw [e2, e3]; exact hdisc)
    refine ⟨n, hn, ?_⟩
    rw [← hnφ, ← coeff_map, hmapMul, map_natCast]
    rw [e2, e3, ← Formalism.L2.Th1.A.uSerEq ℂ_[l] g2 g3] at h1
    exact h1
  obtain ⟨ε, hε1, hεC⟩ := GlobalTheory.T.heightTwo_formalGroup_unramified_multiplier (MaximalUnramifiedExtension l) l σ hU hRes f e hInt w hCoef hσσ hnorm hht
  refine ⟨φ ε, ε.2, hε1, fun n => ?_⟩
  have hs0 : constantCoeff (C ε * ltLog (MaximalUnramifiedExtension l) l) = 0 := by
    rw [map_mul, constantCoeff_ltLog l (by omega), mul_zero]
  have hEq : (uSer g2 g3).subst (C (φ ε) * ltLog ℂ_[l] l) =
      PowerSeries.map φ (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l)) := by
    rw [map_subst_of φ e _ hs0, hme, map_mul, map_C, ltLog_map]
  rw [hEq, coeff_map]
  exact ⟨(coeff n (e.subst (C ε * ltLog (MaximalUnramifiedExtension l) l))).2, by rw [hnφ]; exact hεC n⟩

end GlobalTheory.HondaCM3
end
end
