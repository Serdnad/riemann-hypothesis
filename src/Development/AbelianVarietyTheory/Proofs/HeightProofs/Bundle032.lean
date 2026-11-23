module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle003
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle031
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.HeightCoset

open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies

theorem opNorm_le_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  refine (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans ?_
  gcongr
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i = ∑ j, A i j * x j := rfl
  rw [this, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  gcongr
  exact PiLp.norm_apply_le x j

variable {D : D7}

theorem infMat_mul' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infMat_one' (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) :
    infMat D.sp.cm.sig V.gram θ (1 : GA D V) = 1 := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (1 : GA D V) = 1 := rfl
  simp only [infMat, this, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem finHt_mul (V : HSp D) (x g : GA D V) (hg : g ∈ GinfC V) (v) : finHt V v (x * g) = finHt V v x := by
  have h0 : finHom V g = 1 := hg
  have h1 : finMat D.sp.cm.sig V.gram (x * g) = finMat D.sp.cm.sig V.gram x := by
    rw [finMat_eq, finMat_eq, map_mul, h0, mul_one]
  have h2 : finMat D.sp.cm.sig V.gram (x * g)⁻¹ = finMat D.sp.cm.sig V.gram x⁻¹ := by
    rw [finMat_eq, finMat_eq, map_inv, map_inv, map_mul, h0, mul_one]
  simp only [finHt, finNorm, h1, h2]

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem infNorm_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infNorm θ V τ (x * g) ≤ infNorm θ V τ x * infNorm θ V τ g := by
  unfold infNorm
  rw [infMat_mul', map_mul]
  exact nnnorm_mul_le _ _

theorem infHt_mul_le (τ : D.what₂.Tau) (x g : GA D V) :
    infHt θ V τ (x * g) ≤ infHt θ V τ x * infHt θ V τ g := by
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)) (max_le ?_ ?_)
  · refine (infNorm_mul_le θ V τ x g).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_left _ _)
  · rw [_root_.mul_inv_rev, mul_comm (infHt θ V τ x)]
    refine (infNorm_mul_le θ V τ g⁻¹ x⁻¹).trans (mul_le_mul' ?_ ?_) <;>
      exact le_max_of_le_right (le_max_right _ _)

theorem infNorm_le_normInf (τ : D.what₂.Tau) (g : GA D V) :
    (infNorm θ V τ g : ℝ) ≤ normInf θ V g ∧ (infNorm θ V τ g⁻¹ : ℝ) ≤ normInf θ V g := by
  have h : ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)
      ≤ normInf θ V g :=
    Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
      (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  constructor
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_right (norm_nonneg _)
  · refine (opNorm_le_sum _).trans (le_trans ?_ h)
    gcongr
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem infHt_le_normInf (hV : 0 < V.rank) (τ : D.what₂.Tau) (g : GA D V) :
    (infHt θ V τ g : ℝ) ≤ normInf θ V g := by
  obtain ⟨h1, h2⟩ := infNorm_le_normInf θ V τ g
  haveI : Nonempty (Fin V.rank) := ⟨⟨0, hV⟩⟩
  have h3 : infNorm θ V τ 1 = 1 := by
    unfold infNorm
    rw [infMat_one', map_one]
    exact nnnorm_one
  have h4 : (1 : ℝ) ≤ infNorm θ V τ g * infNorm θ V τ g⁻¹ := by
    have := infNorm_mul_le θ V τ g g⁻¹
    rw [mul_inv_cancel, h3] at this
    exact_mod_cast this
  have h5 : 1 ≤ normInf θ V g := by
    by_contra hc
    push_neg at hc
    have a0 := (infNorm θ V τ g).coe_nonneg
    have b0 := (infNorm θ V τ g⁻¹).coe_nonneg
    nlinarith
  unfold infHt
  push_cast
  exact max_le h5 (max_le h1 h2)

theorem infHt_rank_zero (hV : V.rank = 0) (τ : D.what₂.Tau) (g : GA D V) : infHt θ V τ g = 1 := by
  haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have h : ∀ g, infNorm θ V τ g ≤ 1 := fun g => by
    have := opNorm_le_sum (infMat D.sp.cm.sig V.gram (θ τ) g)
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact_mod_cast this.trans zero_le_one
  exact max_eq_left (max_le (h g) (h g⁻¹))

theorem height_mul_le (x g : GA D V) (hg : g ∈ GinfC V) :
    height θ V (x * g) ≤ height θ V x * ∏ τ, infHt θ V τ g := by
  unfold height
  simp only [finHt_mul V x g hg]
  rw [mul_right_comm, ← Finset.prod_mul_distrib]
  gcongr with τ
  exact infHt_mul_le θ V τ x g

theorem height_le_normInf_pow (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) :
    ∃ M : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ g ∈ GinfC V,
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V (x * g) : ℝ) ≤ C * normInf θ V g ^ M := by
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · refine ⟨0, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have := height_mul_le θ V x g hg
    simp only [infHt_rank_zero θ V hV, Finset.prod_const_one] at this
    rw [pow_zero]
    exact_mod_cast this
  · refine ⟨Fintype.card D.what₂.Tau, fun x => ⟨height θ V x, fun g hg => ?_⟩⟩
    have : (height θ V (x * g) : ℝ) ≤ height θ V x * ∏ τ, (infHt θ V τ g : ℝ) := by
      exact_mod_cast height_mul_le θ V x g hg
    refine this.trans ?_
    gcongr
    rw [← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) fun τ _ => infHt_le_normInf θ V hV τ g

end GlobalTheory.SmoothForms.HeightCoset

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.SmoothForms.NormInf

theorem entrySum_mul_le {n : Type} [Fintype n] (A B : Matrix n n ℂ) :
    ∑ i, ∑ j, ‖(A * B) i j‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ∑ i, ∑ j, ‖B i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j, ‖(A * B) i j‖ ≤ ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖)
          (fun k _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A‖ := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j (1 : ℂ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ n)‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  refine le_trans (le_of_eq ?_) (PiLp.norm_apply_le _ i)
  congr 1
  change _ = (A *ᵥ Pi.single j 1) i
  simp

theorem sum_mul_add_le {ι : Type} [Fintype ι] (a b c d : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, (a i * c i + d i * b i) ≤ (∑ i, (a i + b i)) * ∑ i, (c i + d i) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : c i + d i ≤ ∑ i, (c i + d i) :=
    Finset.single_le_sum (f := fun i => c i + d i) (fun i _ => add_nonneg (hc i) (hd i)) (Finset.mem_univ i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left h (add_nonneg (ha i) (hb i)))
  nlinarith [mul_nonneg (ha i) (hd i), mul_nonneg (hb i) (hc i)]

theorem infMat_mul' {D : D7} (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (V : HSp D) (g h : GA D V) :
    infMat D.sp.cm.sig V.gram θ (g * h) = infMat D.sp.cm.sig V.gram θ g * infMat D.sp.cm.sig V.gram θ h := by
  have : HA.mat (AF D.host.F) D.sp.cm.sig V.gram (g * h) =
    HA.mat (AF D.host.F) D.sp.cm.sig V.gram g * HA.mat (AF D.host.F) D.sp.cm.sig V.gram h := rfl
  simp only [infMat, this, Units.val_mul]
  rw [Matrix.map_mul, Matrix.map_mul]

theorem infHt_le_height {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (g : GA D V) : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height
  refine le_trans ?_ (le_mul_of_one_le_right' (one_le_finprod' fun _ => le_max_left _ _))
  exact Finset.single_le_prod' (f := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ V τ g)
    (fun _ _ => le_max_left _ _) (Finset.mem_univ τ)

end GlobalTheory.SmoothForms.NormInf

namespace GlobalTheory.SmoothForms


open NormInf in
theorem normInf_mul_le_and_le_height :
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
      (∀ g h : GA D V, normInf θ V (g * h) ≤ normInf θ V g * normInf θ V h) ∧
        ∃ C : ℝ, ∀ g : GA D V, normInf θ V g ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) := by
  intro D θ V
  refine ⟨fun g h => ?_, ⟨∑ _τ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (2 : ℝ), fun g => ?_⟩⟩
  · unfold normInf
    simp only [Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin V.rank)))]
    have hn : ∀ (x : GA D V) τ, 0 ≤ ∑ i, ∑ j, ‖infMat D.sp.cm.sig V.gram (θ τ) x i j‖ := fun x τ =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine le_trans ?_ (sum_mul_add_le _ _ _ _ (hn g) (hn g⁻¹) (hn h) (hn h⁻¹))
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [_root_.mul_inv_rev, infMat_mul', infMat_mul']
    exact add_le_add (entrySum_mul_le _ _) (entrySum_mul_le _ _)
  · unfold normInf
    simp only [Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 := infHt_le_height θ V τ g
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans h0
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infNorm θ V τ g⁻¹ ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans h0
    have h3 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g) i j).trans (NNReal.coe_le_coe.2 h1)
    have h4 := (norm_entry_le_opNorm (infMat D.sp.cm.sig V.gram (θ τ) g⁻¹) i j).trans (NNReal.coe_le_coe.2 h2)
    linarith

end GlobalTheory.SmoothForms
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G
open scoped TensorProduct

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}
  (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

local instance gaussStatementOpIsLocalRing : IsLocalRing (Op X la N) :=
  IsLocalization.AtPrime.isLocalRing (Op X la N) (gI X la N)

local instance gaussStatementOpIsDomain : IsDomain (Op X la N) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors

local instance gaussStatementKpField : Field (Kp X la N) :=
  inferInstanceAs (Field (FractionRing (Op X la N)))

local instance gaussStatementKpAlgebra : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la)
    (g := (algebraMap (Op X la N) (FractionRing (Op X la N))).comp
      (algebraMap (X.Ol la) (Op X la N)))
    ((IsFractionRing.injective (Op X la N) (FractionRing (Op X la N))).comp
      (Op.algebraMap_injective X la N))).toAlgebra


theorem _root_.GlobalTheory.T.exists_gaussRing_map_to_completion :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ)
      (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N D' N' : ℕ)
      (σ : T0.TVar D' N' ≃ Idx D j N),
      ∃ (f : T0.Op D' N' la →+* Op X la N) (φ : T0.KTf B.KO D' N' →+* Kp X la N),
        f.Flat ∧ IsLocalHom f ∧
        Ideal.map f (IsLocalRing.maximalIdeal (T0.Op D' N' la)) =
          IsLocalRing.maximalIdeal (Op X la N) ∧
        (∀ x : Op X la N, ∃ a, x - f a ∈ IsLocalRing.maximalIdeal (Op X la N)) ∧
        (∀ o, φ (T0.OpToKT D' N' la o) = algebraMap (Op X la N) (FractionRing (Op X la N)) (f o)) ∧
        (∀ a : B.KO, φ (algebraMap B.KO (T0.KTf B.KO D' N') a) =
          algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a)) ∧
        ∀ q, φ (algebraMap (T0.KTp B.KO D' N') (T0.KTf B.KO D' N') (MvPolynomial.X q)) =
          algebraMap (Op X la N) (FractionRing (Op X la N)) (Tv X la N (σ q)) :=
  GlobalTheory.GaussCompletion.exists_gaussRing_map

end
end
end
