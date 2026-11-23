module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle386
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralPreimageEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ B : Multiset ℂˣ, B.card = r ∧ (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) := by
  first | exact @GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | exact GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL | (intros; apply GlobalTheory.FinZeta.AbsZeta.hasSum_norm_kerGL <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq (a : AF F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = evIHom F a := rfl

def embI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (evIHom F).comp (algebraMap F (AF F))

theorem countable_F : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

def infAd (m : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evIHom_infAd (m : mixedEmbedding.mixedSpace F) : evIHom F (infAd m) = m := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) = m
  exact RingEquiv.apply_symm_apply _ m

theorem mul_infAd {u : AF F} (hu : evIHom F u = 0) (m : mixedEmbedding.mixedSpace F) : u * infAd m = 0 := by
  have h1 : u.1 = 0 := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  show (u.1 * _, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  rw [h1, zero_mul, mul_zero]

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def bI (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))) ℝ (mixedEmbedding.mixedSpace F) :=
  Module.finBasis ℝ (mixedEmbedding.mixedSpace F)

def pI {κ : Type} (ξ : κ → F) : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ :=
  fun ij => Algebra.trace ℝ _ (embI F (ξ ij.1) * bI F ij.2)

def mI {κ : Type} (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (i : κ) :
    mixedEmbedding.mixedSpace F :=
  (-(1 / (2 * Real.pi))) • ∑ j, t (i, j) • bI F j

theorem psi_dot {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {κ : Type} [Fintype κ]
    (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (ξ : κ → F) :
    ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) =
      Complex.exp (((∑ ij, pI ξ ij * t ij : ℝ) : ℂ) * Complex.I) := by
  set a := (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i) with ha
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    rw [evI_eq] at hu
    show u * a = 0
    simp only [ha, dotProduct, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_left_comm, mul_infAd hu, mul_zero]
  rw [hψ.2.2 a hAt, evI_eq]
  have hev : evIHom F a = ∑ i, embI F (ξ i) * mI t i := by

    simp only [ha, dotProduct, map_sum, map_mul, evIHom_infAd, embI, RingHom.comp_apply]
  have htr : Algebra.trace ℝ _ (evIHom F a) = -(1 / (2 * Real.pi)) * ∑ ij, pI ξ ij * t ij := by

    rw [hev, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    simp only [mI, mul_smul_comm, Finset.mul_sum, map_smul, map_sum, smul_eq_mul, pI]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [htr]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

theorem pI_eq_zero {κ : Type} {ξ : κ → F} (h : pI ξ = 0) : ξ = 0 := by
  funext i
  by_contra hne
  have hz : ∀ z, Algebra.trace ℝ _ (embI F (ξ i) * z) = 0 := by
    intro z

    rw [← (bI F).sum_repr z, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, show Algebra.trace ℝ _ (embI F (ξ i) * bI F j) = 0 from congrFun h (i, j),
      smul_zero]
  have h1 := hz (embI F (ξ i)⁻¹)
  rw [← map_mul, mul_inv_cancel₀ hne, map_one, ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)),
    Algebra.trace_algebraMap, mixedEmbedding.finrank, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := F)).ne' h1

theorem pI_zero {κ : Type} : pI (0 : κ → F) = 0 := by
  funext ij
  simp [pI]

theorem coeff_zero {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (c : (κ → F) → ℂ) (hc : Summable fun ξ => ‖c ξ‖)
    (h : ∀ t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ,
      ∑' ξ : κ → F, ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * c ξ = 0) :
    c 0 = 0 := by
  classical
  letI : MeasurableSpace (κ → F) := ⊤
  haveI : MeasurableSingletonClass (κ → F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : Countable F := countable_F
  have hint : Integrable c Measure.count := integrable_count_iff.mpr hc
  have hp : Measurable (pI (F := F) (κ := κ)) := fun _ _ => MeasurableSpace.measurableSet_top
  have key := GlobalTheory.FourierPush.setIntegral_preimage_eq_zero (κ → F) Measure.count c hint
    (κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) pI hp ?_ {0} (measurableSet_singleton 0)
  · have hpre : pI ⁻¹' {0} = ({0} : Set (κ → F)) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨pI_eq_zero, fun h => h ▸ pI_zero⟩
    rw [hpre, integral_singleton] at key
    simpa using key
  · intro l
    have hI : Integrable (fun ξ => Complex.exp ((l (pI ξ) : ℂ) * Complex.I) * c ξ) Measure.count := by
      refine integrable_count_iff.mpr (hc.congr fun ξ => ?_)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [integral_countable hI]
    have hl : ∀ ξ : κ → F, l (pI ξ) = ∑ ij, pI ξ ij * l (fun k => if ij = k then 1 else 0) := by
      intro ξ
      rw [show l (pI ξ) = l.toLinearMap (pI ξ) from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [smul_eq_mul]
    have := h (fun ij => l (fun k => if ij = k then 1 else 0))
    rw [← this]
    refine tsum_congr fun ξ => ?_
    rw [psi_dot hψ, ← hl]
    simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj

theorem theta_inj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ),
    IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd Φ₁ Φ₂ f h₁ h₂
  funext x
  have hs : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) →
      Summable fun ξ : Fin n × Fin d → F => ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    intro Φ hΦ
    have := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    exact this
  have hsum : Summable fun ξ : Fin n × Fin d → F =>
      ‖Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    refine ((hs Φ₁ h₁.1).add (hs Φ₂ h₂.1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
  have key := coeff_zero hψ
    (fun ξ => Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x))
    hsum ?_
  · have h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) + x = x := by
      funext i; simp
    simp only [h0, sub_eq_zero] at key
    exact key
  · intro t
    have hn : ∀ ξ : Fin n × Fin d → F,
        ‖ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i))‖ = 1 := fun ξ => by
      rw [psi_dot hψ]; exact Complex.norm_exp_ofReal_mul_I _
    have hS : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F =>
        ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
          Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) := fun Φ hΦ =>
      Summable.of_norm ((hs Φ hΦ).congr fun ξ => by rw [norm_mul, hn, one_mul])
    have hT : ∀ Φ, IsDatum M ψ crd Φ f →
        ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) * ∑' ξ : Fin n × Fin d → F,
          ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
            Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) =
          f (crd (M.co.e.symm (x, fun i => infAd (mI t i)))) := by
      intro Φ hΦ
      rw [← hΦ.2 (M.co.e.symm (x, fun i => infAd (mI t i))), ← tsum_mul_left]
      simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply,
        AddChar.map_add_eq_mul]
      refine tsum_congr fun ξ => ?_
      ring
    have hne : ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) ≠ 0 := by
      intro h0
      have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i)))
        (-(⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))))
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have e2 := mul_left_cancel₀ hne ((hT Φ₁ h₁).trans (hT Φ₂ h₂).symm)
    simp only [mul_sub]
    rw [(hS Φ₁ h₁.1).tsum_sub (hS Φ₂ h₂.1), e2, sub_self]

end GlobalTheory.ThetaInj
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ) (T.gram.map (incA D)))
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a
      = ∑ b, ∑ d, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_mul_submatrix {A : Type} [CommRing A] {m d : ℕ} (e : Fin m ≃ Fin d) (P : Matrix (Fin d) (Fin d) A)
    (K : Matrix (Fin m) (Fin m) A) : (P * K.submatrix e.symm e.symm).trace = (P.submatrix e e * K).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  simp

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun _ _ => S.herm.eq _ _

theorem gram_map_herm (S : HSp D) : ((S.gram.map (incA D)).map (cA D))ᵀ = S.gram.map (incA D) := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem gram_inv_mul (T : HSp D) : T.gram⁻¹.map (incA D) * T.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne _))]; simp

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (c' : A →+* A)
    (hc : ∀ a, c a = c' a) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c' * JBᵀ).trace := by
  rw [hTens_eq_trace]
  congr 3
  ext i j
  exact hc _

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sgn_gram (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]



theorem symp_eq (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (JV : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (JW : Matrix (Fin d) (Fin d) D.host.E)
    (hJ : JV = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : JW = D.host.xi0 • reindex e e X.gramᵀ)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) → WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (u w : Matrix (Fin S.rank) (Fin d) (AE D)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW) u w = symplO (sgn ε S) X (cS u) (cS w) := by
  have hGs : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = (sgn ε S).gram.map (incA D) := by
    rw [← sgn_gram]; rfl
  have hJA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV = -(sgn ε S).gram.map (incA D) := by
    rw [hJ, sgn_gram]
    cases ε <;> ext i j <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hJB : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW)ᵀ =
      incA D D.host.xi0 • (X.gram.map (incA D)).submatrix e.symm e.symm := by
    rw [hJW]; ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  unfold GlobalTheory.WeilM.symp symplO
  rw [hTens_eq_trace' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (cA D) (fun _ => rfl), hO_eq_trace, hcS, hcS, hGs, hJA, hJB]
  have hinv := gram_inv_mul (sgn ε S)
  have hh := gram_map_herm (sgn ε S)
  have hW : ((wᵀ.submatrix e id).map (cA D))ᵀ = (w.map (cA D)).submatrix id e := rfl
  congr 1
  rw [Matrix.map_mul, Matrix.transpose_mul, hh, ← Matrix.mul_assoc _ _ (((wᵀ.submatrix e id).map (cA D))ᵀ), hinv,
    Matrix.one_mul, hW]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg,
    smul_eq_mul, trace_mul_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc (uᵀ.submatrix e id * _), Matrix.trace_mul_comm (uᵀ.submatrix e id * _)]
  ring

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem invOf_two' {D : D7} : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem isDatum_rho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  intro D ψ θ _ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW _ _ _ M _ cS hcS Φ f hD w
  refine ⟨?_, fun u => ?_⟩
  · have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
    exact GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd w Φ hD.1
  · rw [GlobalTheory.BigDat.rho_rho M.co ψ u w Φ, GlobalTheory.WeilM.thetaSum_smul, hD.2 (u + w)]
    unfold heisO symplOH
    rw [symp_eq ε S X e Vs.J Ws.J hJ hJW cS hcS u w, map_add (f := _), invOf_two']

end GlobalTheory.SquareAgree.HeisCov
end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct


theorem _root_.GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  first | exact @GlobalTheory.HoweGlobal.TensorMap.exists_tensL | exact GlobalTheory.HoweGlobal.TensorMap.exists_tensL | (intros; apply GlobalTheory.HoweGlobal.TensorMap.exists_tensL <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory.TrIdem

theorem levelFam_open_le : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  intro D V T U hu v
  by_cases hvu : v = U.u
  · subst hvu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.iwahori_le⟩
  by_cases hv : v ∈ T.S
  · have h := levelFam_of_mem T U hu ⟨v, hv⟩
    simp only at h
    rw [h, kerSub]
    refine ⟨?_, Subgroup.map_subtype_le _⟩
    rw [Subgroup.coe_map]
    exact (isOpen_stabLoc _ _ _ v).isOpenMap_subtype_val _ (T.frame ⟨v, hv⟩).isOpen_ker_red
  · rw [levelFam_of_notMem T U hv hvu]
    exact ⟨isOpen_stabLoc _ _ _ v, le_refl _⟩

end GlobalTheory.TrIdem
end
