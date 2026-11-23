module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle328
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle241
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

section

namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem one_inf_div {E : Type} [Field E] [NumberField E] (𝔪 𝔫 : Ideal (𝓞 E)) (h𝔫 : 𝔫 ≠ ⊥)
    (hc : IsCoprime 𝔪 𝔫) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫) = 𝔪 := by
  have h𝔫' : (𝔫 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  apply le_antisymm
  · obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 (inf_le_left : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ⊓ _ ≤ 1)
    rw [← hI]
    have h2 : (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≤ (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) / 𝔫 := hI ▸ inf_le_right
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫', ← FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_le_coeIdeal] at h2
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]
    have hs : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.isCoprime_iff_sup_eq.1 hc
    calc I = I * (𝔪 ⊔ 𝔫) := by rw [hs, Ideal.mul_top]
      _ = I * 𝔪 ⊔ I * 𝔫 := Ideal.mul_sup _ _ _
      _ ≤ 𝔪 := sup_le (by first | exact Ideal.mul_le_right | exact Ideal.mul_le_left) h2
  · refine le_inf FractionalIdeal.coeIdeal_le_one ?_
    rw [FractionalIdeal.le_div_iff_mul_le h𝔫']
    calc (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * 𝔫 ≤ 𝔪 * 1 := mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = 𝔪 := mul_one _

theorem mul_inf {E : Type} [Field E] [NumberField E] (A X Y : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hA : A ≠ 0) : A * (X ⊓ Y) = A * X ⊓ A * Y := by
  apply le_antisymm
  · exact le_inf (mul_le_mul' le_rfl inf_le_left) (mul_le_mul' le_rfl inf_le_right)
  · have e : A * X ⊓ A * Y = A * (A⁻¹ * (A * X ⊓ A * Y)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    rw [e]
    refine mul_le_mul' le_rfl (le_inf ?_ ?_)
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * X) := mul_le_mul' le_rfl inf_le_left
        _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    · calc A⁻¹ * (A * X ⊓ A * Y) ≤ A⁻¹ * (A * Y) := mul_le_mul' le_rfl inf_le_right
        _ = Y := by rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]

variable (D : D7)

def skewEnt (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem mem_skewLat_iff (𝔪 : Ideal (𝓞 D.host.E)) (N : ℕ) (x : Fin N → D.host.E) :
    x ∈ skewLat D 𝔪 N ↔ ∀ i, x i ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [skewLat, skewEnt, Submodule.mem_pi, Set.mem_univ, true_implies]

theorem mem_YYl_skew_iff (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) (x : Matrix (Fin d) (Fin a) D.host.E) :
    x ∈ YYl D (stdL D a) (skewLat D 𝔪 d) ↔
      ∀ i j, x i j ∈ ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨c, hc, A, hA, rfl⟩ := hB
      have hAe : ∀ i j, A i j ∈ (skewEnt D 𝔪 : Submodule (𝓞 D.host.E) D.host.E) := by
        induction hA using Submodule.span_induction with
        | mem A hA =>
          intro i j
          have hj : (Pi.single j (1 : D.host.E) : Fin a → D.host.E) ∈ stdL D a := by
            simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies]
            intro k
            by_cases hk : k = j
            · subst hk; simp [Submodule.one_eq_range]
            · simp [Pi.single_apply, hk]
          have h := (mem_skewLat_iff D 𝔪 d _).1 (hA _ hj) i
          simpa [Matrix.mulVec_single] using h
        | zero => intro i j; simp
        | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
        | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
      intro i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact FractionalIdeal.mul_mem_mul hc (hAe i j)
    | zero => intro i j; simp
    | add A B _ _ h1 h2 => intro i j; simpa using add_mem (h1 i j) (h2 i j)
    | smul r A _ h => intro i j; simpa using Submodule.smul_mem _ r (h i j)
  · intro hx
    rw [Matrix.matrix_eq_sum_single x]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hij := hx i j
    rw [FractionalIdeal.coe_mul] at hij
    refine Submodule.mul_induction_on (C := fun r => Matrix.single i j r ∈ YYl D (stdL D a) (skewLat D 𝔪 d)) hij ?_ ?_
    · intro m hm n hn
      refine Submodule.subset_span ⟨m, hm, Matrix.single i j n, Submodule.subset_span fun v hv => ?_, ?_⟩
      · refine (mem_skewLat_iff D 𝔪 d _).2 fun k => ?_
        have hvj : v j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
          simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv
          exact hv j
        obtain ⟨o, ho⟩ := Submodule.mem_one.1 hvj
        by_cases hk : k = i
        · subst hk
          simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, true_and]
          rw [Finset.sum_eq_single j (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
          simp only [if_true]
          rw [← ho, mul_comm, ← Algebra.smul_def]
          exact Submodule.smul_mem _ o hn
        · have hk' : i ≠ k := Ne.symm hk
          simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hk']
      · rw [Matrix.smul_single, smul_eq_mul]
    · intro x y hx hy
      simpa [Matrix.single_add] using add_mem hx hy

theorem La_skew_eq_map (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) =
      (matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)).map (ptHom D ⊤ δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D ⊤ δ a d c A⟩
    have := (mem_YYl_skew_iff D 𝔪 a d A).1 hA i j
    rw [Matrix.smul_apply, smul_eq_mul, ← coe_alg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ this
  · rintro _ ⟨z, hz, rfl⟩
    refine AddSubgroup.subset_closure ⟨δ, (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ δ).2 ⟨1, trivial, by simp⟩, z,
      (mem_YYl_skew_iff D 𝔪 a d z).2 hz, ?_⟩
    rfl

end GlobalTheory.SkewIndex

namespace GlobalTheory.SkewIndex

open GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs GlobalTheory.ThetaLatticePoints GlobalTheory.MatrixLatticeIndex GlobalTheory.NormSum.MovedLattice

theorem index_inter_skew : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → ∀ (a d : ℕ), ((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index = Ideal.absNorm 𝔪 ^ (a * d) := by
  intro D δ hC 𝔪 h𝔪 hcop a d
  have hδ : δ ≠ 0 := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ hC).2.1
  have hN : Ideal.absNorm (D.host.conj • 𝔪) = Ideal.absNorm 𝔪 := UnusedSlot33.HK.absNorm_smul D.host 𝔪
  have h𝔫 : (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) ≠ ⊥ := by
    intro h
    apply h𝔪
    rw [← Ideal.absNorm_eq_zero_iff, ← hN, h, Ideal.absNorm_bot]
  have hA := inverseHalfDifferent_ne_zero D
  have h𝔪' : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h𝔫' : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 h𝔫
  have hJ : D.host.AA0 * skewEnt D 𝔪 ≠ 0 := mul_ne_zero hA (div_ne_zero h𝔪' h𝔫')
  have hcoef : coefLat D ⊤ = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [coefLat_eq, ext, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]

  have hF : D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
        (D.host.AA0 * skewEnt D 𝔪) := by
    rw [show D.host.AA0 ⊓ D.host.AA0 * skewEnt D 𝔪 = D.host.AA0 * 1 ⊓ D.host.AA0 * skewEnt D 𝔪 by rw [mul_one]]
    rw [← mul_inf _ _ _ hA, skewEnt, one_inf_div 𝔪 _ h𝔫 hcop, mul_left_comm, mul_div_cancel₀ _ h𝔫']
  have he : ∀ J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
      ((((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * J :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E) =
        (D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • (J : Submodule (𝓞 D.host.E) D.host.E) := by
    intro J
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  have hinf : (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup ⊓
      ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup =
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) • ((D.host.AA0 * skewEnt D 𝔪 :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E)).toAddSubgroup := by
    rw [← he, ← hF, FractionalIdeal.coe_inf]
    rfl
  show (La0 D (tor0 D ⊤ δ) a d).relIndex (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) = _
  rw [La0_eq_map, La_skew_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (ptHom_injective D ⊤ hδ a d)]
  have hc := card_matIn D a d ((D.host.AA0 * skewEnt D 𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    Submodule (𝓞 D.host.E) D.host.E) (coefLat D ⊤)
  rw [hcoef, ← AddSubgroup.inf_relIndex_right, hinf, relIndex_smul _ hJ _ h𝔫, hN] at hc
  rw [show lat0 D ⊤ a d = matIn D a d (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) by rw [lat0, hcoef]]
  exact hc

end GlobalTheory.SkewIndex
end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.WeightPart

variable {S ι : Type} [Ring S] [Fintype ι] {ε : ι → S} {w : ι → ℤ}

def dg (ε : ι → S) (w : ι → ℤ) (x : S) : S := ∑ a, ∑ b, if w a = w b then ε a * x * ε b else 0

theorem ext_sand (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : ∀ a b, ε a * x * ε b = ε a * y * ε b) : x = y := by
  have e : ∀ z : S, z = ∑ a, ∑ b, ε a * z * ε b := fun z => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  rw [e x, e y]
  simp only [h]

theorem sand_mul (he : CompleteOrthogonalIdempotents ε) (x y : S) (a b : ι) :
    ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
  have e : ∀ c, (ε a * x * ε c) * (ε c * y * ε b) = ε a * x * ε c * (y * ε b) := fun c => by
    rw [mul_assoc (ε c) y, ← mul_assoc _ (ε c) (y * ε b), mul_assoc _ (ε c) (ε c), (he.idem c).eq]
  simp only [e]
  rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
  simp only [mul_one, mul_assoc]

theorem sand_dg (he : CompleteOrthogonalIdempotents ε) (x : S) (a b : ι) :
    ε a * dg ε w x * ε b = if w a = w b then ε a * x * ε b else 0 := by
  classical
  rw [dg, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single a, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_eq_single b]
  · split_ifs
    · rw [← mul_assoc, ← mul_assoc, (he.idem a).eq, mul_assoc _ (ε b), (he.idem b).eq]
    · simp
  · intro c _ hc
    split_ifs
    · rw [mul_assoc, mul_assoc _ (ε c), he.ortho hc, mul_zero, mul_zero]
    · simp
  · simp
  · intro c _ hc
    rw [Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
    intro d _
    split_ifs
    · rw [← mul_assoc, ← mul_assoc, he.ortho hc.symm, zero_mul, zero_mul]
    · simp
  · simp

theorem dg_mul_dg (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : x * y = 1)
    (hx : ∀ a b, w a < w b → ε a * x * ε b = 0) (hy : ∀ a b, w a < w b → ε a * y * ε b = 0) :
    dg ε w x * dg ε w y = 1 := by
  refine ext_sand he fun a b => ?_
  by_cases hab : w a = w b
  · rw [← h, sand_mul he, sand_mul he]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    rcases lt_trichotomy (w a) (w c) with h1 | h1 | h1
    · rw [if_neg h1.ne, hx a c h1, zero_mul, zero_mul]
    · rw [if_pos h1, if_pos (h1 ▸ hab)]
    · rw [if_neg h1.ne', hy c b (hab ▸ h1), zero_mul, mul_zero]
  · rw [mul_one, he.ortho (fun e => hab (congrArg w e)), sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    by_cases h1 : w a = w c
    · rw [if_neg (show ¬ w c = w b from h1 ▸ hab), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem exists_weightPart : ∀ {S ι : Type} [Ring S] [Fintype ι] (st : S →+ S) (ε : ι → S) (w : ι → ℤ) (τ : ι → ι), (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → CompleteOrthogonalIdempotents ε → (∀ a, st (ε a) = ε (τ a)) → (∀ a, w (τ a) = -w a) → (∀ a, τ (τ a) = a) → ∀ x y : S, x * y = 1 → y * x = 1 → st x = y → (∀ a b, w a < w b → ε a * x * ε b = 0) → (∀ a b, w a < w b → ε a * y * ε b = 0) → ∃ m m' : S, m * m' = 1 ∧ m' * m = 1 ∧ st m = m' ∧ (∀ a b, w a ≠ w b → ε a * m * ε b = 0) ∧ (∀ a b, w a ≠ w b → ε a * m' * ε b = 0) ∧ x * m' - 1 ∈ raise ε w 0 ∧ ∀ S₀ : Subring S, (∀ a, ε a ∈ S₀) → x ∈ S₀ → y ∈ S₀ → m ∈ S₀ ∧ m' ∈ S₀ := by
  intro S ι _ _ st ε w τ hst hss he hε hw hτ x y hxy hyx hs hx hy
  have hm : ∀ z a b, w a ≠ w b → ε a * dg ε w z * ε b = 0 := fun z a b h => by rw [sand_dg he, if_neg h]
  have h1 := dg_mul_dg he hxy hx hy
  refine ⟨dg ε w x, dg ε w y, h1, dg_mul_dg he hyx hy hx, ?_, hm x, hm y, ?_, ?_⟩
  · have key : ∀ z a b, ε a * st z * ε b = st (ε (τ b) * z * ε (τ a)) := fun z a b => by
      rw [hst, hst, hε, hε, hτ, hτ, mul_assoc]
    refine ext_sand he fun a b => ?_
    rw [key, sand_dg he, sand_dg he, ← hs, key, hw, hw]
    by_cases h : w a = w b
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun e => h (neg_inj.1 e).symm), map_zero]
  · intro a b hab
    have hab' : w a ≤ w b := by simpa using hab
    rw [← h1, ← sub_mul, sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : w c = w b
    · rw [mul_sub, sub_mul, sand_dg he]
      split_ifs with h2
      · rw [sub_self, zero_mul]
      · rw [hx a c (lt_of_le_of_ne (h ▸ hab') h2), sub_self, zero_mul]
    · rw [hm y c b h, mul_zero]
  · intro S₀ h0 hx0 hy0
    have : ∀ z ∈ S₀, dg ε w z ∈ S₀ := fun z hz =>
      sum_mem fun a _ => sum_mem fun b _ => by
        split_ifs
        · exact mul_mem (mul_mem (h0 a) hz) (h0 b)
        · exact zero_mem _
    exact ⟨this x hx0, this y hy0⟩

end GlobalTheory.WeightPart
end

section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.exists_invariant_hermitianForm_cuspidalRep : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  first | exact @GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | exact GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian | (intros; apply GlobalTheory.GelfandKazhdanHerm.exists_invariant_hermitian <;> assumption)
end
