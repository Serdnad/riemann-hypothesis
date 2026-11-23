module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle705
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle110
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle196
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle088
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle150
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle152
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle214
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle215
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle213
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.OddTheta

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = latticeArea L := by
  have hA := latticeArea_eq L
  have hpos := latticeArea_pos L
  have key : ∀ w₁ ∈ L.lattice, ∀ w₂ ∈ L.lattice, ∃ k : ℤ,
      ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
    intro w₁ hw₁ w₂ hw₂
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 hw₁
    obtain ⟨m', n', rfl⟩ := PeriodPair.mem_lattice.1 hw₂
    refine ⟨m * n' - n * m', ?_⟩
    simp [Complex.mul_im, Complex.mul_re]
    ring
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨hA ▸ hpos, L.ω₁, (h _).2 L.ω₁_mem_lattice, L.ω₂, (h _).2 L.ω₂_mem_lattice, hA⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := key w₁ ((h _).1 hw₁) w₂ ((h _).1 hw₂)
  rw [hk, abs_mul, ← hA] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left hpos.le hk1

theorem wpF_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) (z : ℂ) :
    wpF Λ z = L.weierstrassP z := by
  apply GlobalTheory.LatticeInvariants.wpF_eq <;> assumption

theorem law_iff (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (ω z : ℂ) :
    U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z ↔
      G (z + ω) = sigmaSign L ω * Complex.exp (Real.pi * latticeForm L z ω +
        Real.pi * latticeForm L ω ω / 2) * G z := by
  have hs : (if ω / 2 ∈ Λ then (1 : ℂ) else -1) = sigmaSign L ω := by
    by_cases hw : ω / 2 ∈ Λ
    · rw [if_pos hw, sigmaSign_of_mem L ((h _).1 hw)]
    · rw [if_neg hw, sigmaSign_of_notMem L (fun hh => hw ((h _).2 hh))]
  have hU : U1 Λ ω G z = G (z + ω) *
      (Complex.exp (Real.pi * latticeForm L z ω + Real.pi * latticeForm L ω ω / 2))⁻¹ := by
    unfold U1
    rw [area_eq L Λ h, ← Complex.exp_neg]
    congr 2
    simp only [latticeForm]
    ring
  rw [hU, hs, mul_inv_eq_iff_eq_mul₀ (Complex.exp_ne_zero _)]
  constructor <;> intro hh <;> rw [hh] <;> ring

theorem eq_deriv_mul (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) (z : ℂ) :
    G z = deriv G 0 * canonicalSigma L z := by
  have hlaw' : ∀ w ∈ L.lattice, ∀ z, G (z + w) = sigmaSign L w *
      Complex.exp (Real.pi * latticeForm L z w + Real.pi * latticeForm L w w / 2) * G z :=
    fun w hw z => (law_iff L Λ h G w z).1 (hlaw w ((h w).2 hw) z)
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L hG hlaw'
  have hGf : G = fun z => c * canonicalSigma L z := funext hc
  have hd : deriv G 0 = c := by
    rw [hGf]
    exact ((hasDerivAt_canonicalSigma_zero L).const_mul c).deriv.trans (mul_one c)
  rw [hd]
  exact hc z

theorem canonicalSigma_spec (L : PeriodPair) (Λ : AddSubgroup ℂ)
    (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    Differentiable ℂ (canonicalSigma L) ∧ deriv (canonicalSigma L) 0 = 1 ∧
      (∀ z, canonicalSigma L (-z) = -canonicalSigma L z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω (canonicalSigma L) z =
        (if ω / 2 ∈ Λ then 1 else -1) * canonicalSigma L z := by
  refine ⟨differentiable_canonicalSigma L, (hasDerivAt_canonicalSigma_zero L).deriv,
    canonicalSigma_neg L, ?_⟩
  intro ω hω z
  exact (law_iff L Λ h _ ω z).2 (canonicalSigma_add L ((h ω).1 hω) z)

theorem sgStar_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    sgStar Λ = canonicalSigma L := by
  have hP : ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ deriv G 0 = 1 ∧ (∀ z, G (-z) = -G z) ∧
      ∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z :=
    ⟨_, canonicalSigma_spec L Λ h⟩
  unfold sgStar
  obtain ⟨hd, h1, -, hl⟩ := Classical.epsilon_spec hP
  funext z
  rw [eq_deriv_mul L Λ h _ hd hl z, h1, one_mul]

theorem exists_periodPair (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hind, rfl⟩ := hΛ
  refine ⟨⟨w₁, w₂, hind⟩, fun z => ?_⟩
  show z ∈ AddSubgroup.closure {w₁, w₂} ↔ z ∈ Submodule.span ℤ {w₁, w₂}
  rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]

theorem sgStar_laws : ∀ (Λ : AddSubgroup ℂ), (∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) → (Differentiable ℂ (sgStar Λ) ∧ deriv (sgStar Λ) 0 = 1 ∧ (∀ z, sgStar Λ (-z) = -sgStar Λ z) ∧ ∀ ω ∈ Λ, ∀ z, U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z) ∧ (∀ z, sgStar Λ z = 0 ↔ z ∈ Λ) ∧ (∀ G : ℂ → ℂ, Differentiable ℂ G → (∀ ω ∈ Λ, ∀ z, U1 Λ ω G z = (if ω / 2 ∈ Λ then 1 else -1) * G z) → ∀ z, G z = deriv G 0 * sgStar Λ z) ∧ (∀ u v : ℂ, u ∉ Λ → v ∉ Λ → (wpF Λ u - wpF Λ v) * (sgStar Λ u ^ 2 * sgStar Λ v ^ 2) = -(sgStar Λ (u + v) * sgStar Λ (u - v))) ∧ ∀ c : ℂ, c ≠ 0 → ∀ z, sgStar (Λ.map (AddMonoidHom.mulLeft c)) (c * z) = c * sgStar Λ z := by
  intro Λ hΛ
  obtain ⟨L, h⟩ := exists_periodPair Λ hΛ
  have hσ := sgStar_eq L Λ h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    exact canonicalSigma_spec L Λ h
  · intro z
    rw [hσ, canonicalSigma_eq_zero_iff L, h]
  · intro G hG hl z
    rw [hσ]
    exact eq_deriv_mul L Λ h G hG hl z
  · intro u v hu hv
    have hu' : u ∉ L.lattice := fun hh => hu ((h u).2 hh)
    have hv' : v ∉ L.lattice := fun hh => hv ((h v).2 hh)
    have hne : canonicalSigma L u ^ 2 * canonicalSigma L v ^ 2 ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hu'))
        (pow_ne_zero _ ((canonicalSigma_eq_zero_iff L).not.2 hv'))
    rw [wpF_eq L Λ h, wpF_eq L Λ h, hσ, weierstrassP_sub_weierstrassP_canonicalSigma L hu' hv']
    exact div_mul_cancel₀ _ hne
  · intro c hc z
    have hhom := isHomothetic_scalePeriods L c hc
    have h' : ∀ x, x ∈ Λ.map (AddMonoidHom.mulLeft c) ↔ x ∈ (scalePeriods L c hc).lattice := by
      intro x
      rw [AddSubgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (hhom y).2 ((h y).1 hy)
      · intro hx
        refine ⟨c⁻¹ * x, (h _).2 ((hhom _).1 ?_), ?_⟩
        · rwa [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
        · simp [hc]
    rw [sgStar_eq (scalePeriods L c hc) _ h', hσ, hhom.canonicalSigma_mul]

end GlobalTheory.OddTheta
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.JointHarm

namespace GlobalTheory.HarmonicShape

theorem weight_eq_wtK (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ)
    (μ : Ix p q → ℚ) (P : Pol p q n 0) (h1 : IsHW (fockAct1 p q n 0) μ P)
    (h2 : P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am))
    (h3 : KilledByLower (fockAct1 p q n 0) P) : μ = wtK n ap am := by
  have hj : P ∈ jointHW μ (wtH n ap am) := by
    refine ⟨⟨h1.2, h2⟩, ⟨fun a b => ?_, fun a b => by simp⟩, fun _ j => j.elim0, fun i => i.elim0⟩
    have := h3 a b
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FockSingularValues.fockAct1_lower, neg_eq_zero] at this
    exact this
  obtain ⟨α, β, γ, δ, ⟨-, -, -, -, a1, b1, c1, d1, -, -, -, -, e1, e2, e3, -⟩, -⟩ :=
    four_of_joint h1.1 hj
  funext x
  rcases x with i | j
  · have hi := i.2
    have u := e1 i
    have v := e3 ⟨i.1, by omega⟩
    rw [b1 _ (by simp)] at u
    rw [d1 _ ((min_le_left _ _).trans (by rw [Fin.val_rev]; dsimp only; omega))] at v
    simp only [shiftNu, cPair, wtH, hi, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith
  · have hj := j.2
    have hr := j.rev.2
    have u := e2 j
    have v := e3 (Fin.rev ⟨j.rev.1, by omega⟩)
    have hp : ¬ (Fin.rev (⟨j.rev.1, by omega⟩ : Fin n)).1 < p := by
      rw [Fin.val_rev]; dsimp only; omega
    rw [c1 _ (by simp)] at u
    rw [a1 _ ((min_le_left _ _).trans (not_lt.1 hp))] at v
    simp only [shiftNu, cPair, wtH, dif_neg hp, Fin.rev_rev, hr, dif_pos, Fin.eta] at u v
    simp only [wtK]
    push_cast at u v
    linarith

end GlobalTheory.HarmonicShape
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockExtGroup

theorem pi_comm {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (g, 1) (F.π (1, h) x) = F.π (1, h) (F.π (g, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem comm_and_extend : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  intro p q n T0 T1 T2 F hn D τ M j I v₀ hτ hM hv₀ hI hJ
  obtain ⟨hfin, -, -, hirr⟩ := GlobalTheory.CompactCoverIrr.hcMod_finite_irr n hn T2 τ M j hτ hM ⟨v₀, 0, hv₀⟩
  obtain ⟨hF, -, hder⟩ := GlobalTheory.FockEmbExp.fock_derived p q n 0 T0 T1 T2 F
  let σ : URep T2 :=
    { H := F.H
      π := F.π.comp (MonoidHom.inr _ _)
      isom := fun _ x => F.isom _ x
      cont := fun x => (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id)) }
  have h1 : ∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
      F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v')) := by
    intro h x v v' hv
    have hK : h ∈ T2.Kset := by
      rintro (a | a) (b | b) hab
      · exact (hab trivial).elim
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
    let j₂ : M.V →ₗ[ℂ] σ.H := F.ι ∘ₗ I ∘ₗ TensorProduct.mk ℂ D.HK.V M.V x
    obtain ⟨w, hw1, hw2⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie n 0 T2
      (GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T2) τ σ M.V (fun Y => M.act Y) j j₂
      (fun Y hY _ w => ⟨hM.2.2 Y hY w, by
        have h2 := hder Y hY (I (x ⊗ₜ w))
        have h3 : fockAct2 p q n 0 Y (I (x ⊗ₜ w)) = I (x ⊗ₜ M.act Y w) := hI.2 Y x w
        rw [h3] at h2
        exact h2⟩) h hK v
    obtain rfl : v' = w := hM.1 (hv.trans hw1)
    exact hw2
  refine ⟨h1, ?_⟩
  let N : Submodule ℂ M.V :=
    { carrier := {v | ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
        ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)}
      add_mem' := by
        rintro a b ⟨J, hJ1, hJ2⟩ ⟨J', hJ1', hJ2'⟩
        exact ⟨J + J', fun x => by simp [hJ1, hJ1', TensorProduct.tmul_add],
          fun g y => by simp [hJ2, hJ2']⟩
      zero_mem' := ⟨0, fun x => by simp, fun g y => by simp⟩
      smul_mem' := by
        rintro c a ⟨J, hJ1, hJ2⟩
        exact ⟨c • J, fun x => by simp [hJ1, TensorProduct.tmul_smul],
          fun g y => by simp [hJ2]⟩ }
  rcases hirr N (by
    rintro h v ⟨J, hJ1, hJ2⟩ v' hv
    refine ⟨F.π (1, h) ∘L J, fun x => ?_, fun g y => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, hJ1, h1 h x v v' hv]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pi_comm, hJ2]) with h | h
  · have : v₀ ∈ N := hJ
    rw [h] at this
    exact (hv₀ this).elim
  · intro v
    have : v ∈ N := h ▸ Submodule.mem_top
    exact this

end GlobalTheory.FockExtGroup
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNConj

theorem slash_neg_one_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) : f ∣[k] (-1 : SL(2, ℤ)) = f := by
  ext τ
  simp only [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul]
  have : UpperHalfPlane.denom ((-1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = (-1) * UpperHalfPlane.denom ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := by
    simp [UpperHalfPlane.denom]
  rw [this, mul_zpow, (hk.neg).neg_one_zpow]
  simp [UpperHalfPlane.denom]

theorem redGL_neg_one (N : ℕ) : redGL N (-1) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, Matrix.SpecialLinearGroup.coe_neg]

theorem redGL_gamma (N : ℕ) (γ : SL(2, ℤ)) (h : γ ∈ CongruenceSubgroup.Gamma N) : redGL N γ = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at h
  obtain ⟨h00, h01, h10, h11⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [redGL, h00, h01, h10, h11]

end GlobalTheory.FNConj

namespace GlobalTheory.FNConj

theorem main : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k →
    (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) →
    ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧
      ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  intro g N _ d k f hg hk hinv hq
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨hvact, hgact, hvass, -, -, -, -, -, -⟩ := GlobalTheory.WpFam.Act.rightActions N
  obtain ⟨c₁, c₂, hsep⟩ := GlobalTheory.T.exists_weierstrassP_family_separating_gl2ZMod N
  obtain ⟨-, hadd, hsmul, -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N 1)
  obtain ⟨-, hadd', hsmul', -⟩ := GlobalTheory.QFam.isFam_algebra (GL (Fin 2) (ZMod N)) (gact N (dg d))
  obtain ⟨qc, qadd, -, qmul, -⟩ := GlobalTheory.QFam.qConj_ring g N hN

  set t : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ +
    (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ with ht
  set t' : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α => t (α * dg d) with ht'
  have hw : ∀ e : Fin 2 → ZMod N, IsFam (gact N 1) 2 (fun α => wp N (vmul e α)) := fun e => by
    have := (GlobalTheory.WpFamGL.main N 1 e).1
    simpa only [mul_one] using this
  have hw' : ∀ e : Fin 2 → ZMod N, IsFam (gact N (dg d)) 2 (fun α => wp N (vmul e (α * dg d))) := fun e =>
    (GlobalTheory.WpFamGL.main N (dg d) e).1
  have htF : IsFam (gact N 1) 2 t :=
    (hadd _ _ _ (hadd _ _ _ (hw _) (hsmul _ _ _ (hw _))).1 (hsmul _ _ _ (hw _))).1
  have htF' : IsFam (gact N (dg d)) 2 t' :=
    (hadd' _ _ _ (hadd' _ _ _ (hw' _) (hsmul' _ _ _ (hw' _))).1 (hsmul' _ _ _ (hw' _))).1
  have hqw : ∀ (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (wp N (vmul e α)) (wp N (vmul e (α * dg d))) := fun e α => by
    rw [← hvass]
    exact (GlobalTheory.WpFam.ConjExp.qConj_torsion N g d hg (vmul e α)).1
  have hqn : ∀ (c : ℕ) (e : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)),
      QConj g N (fun τ => (c : ℂ) * wp N (vmul e α) τ) (fun τ => (c : ℂ) * wp N (vmul e (α * dg d)) τ) := by
    intro c e α
    have := qmul _ _ _ _ (qc (c : ℂ)) (hqw e α)
    simpa only [map_natCast] using this
  have htq : ∀ α, QConj g N (t α) (t' α) := fun α =>
    qadd _ _ _ _ (qadd _ _ _ _ (hqw _ α) (hqn c₁ _ α)) (hqn c₂ _ α)

  obtain ⟨F, hF, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N (k : ℤ) f hinv
  have hFneg : ∀ α, F (-α) = F α := fun α => by
    have h1 := hF α (-1)
    rw [slash_neg_one_even (by exact_mod_cast hk.natCast) (F α)] at h1
    rw [h1, gact_one, redGL_neg_one, mul_neg_one]
  have hsepF : ∀ i j, t i = t j → F i = F j := fun i j h => by
    rcases hsep i j h with rfl | rfl
    · rfl
    · exact hFneg j
  have hFq : ∀ i, ∃ a, HasQ N (F i) a := fun i => by
    rcases hF0 i with ⟨γ, rfl⟩ | h0
    · rw [hFγ]; exact hq γ
    · refine ⟨fun _ => 0, fun τ => ?_⟩
      rw [h0]; simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  obtain ⟨F', hF', hFF'⟩ := GlobalTheory.T.conjugate_modularFamily_along_separatingFamily g (GL (Fin 2) (ZMod N)) (gact N 1) (gact N (dg d)) 2 k N t t' F hN
    (IsRAct.actBij (hgact 1)) (IsRAct.actBij (hgact (dg d))) htF htF' hF hsepF htq hFq
  have hslash : ∀ γ : SL(2, ℤ), F' 1 ∣[(k : ℤ)] γ = F' (dg d * redGL N γ * (dg d)⁻¹) := fun γ => by
    rw [hF' 1 γ, gact, one_mul]
  refine ⟨F' 1, fun γ hγ => ?_, fun γ γ' hγγ' => ?_⟩
  · rw [hslash, redGL_gamma N γ hγ, mul_one, mul_inv_cancel]
  · rw [hslash, hγγ', mul_inv_cancel_right, ← hFγ]
    exact hFF' _

end GlobalTheory.FNConj
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  first | exact @GlobalTheory.EisM.sum_slz_repL_Vo | exact GlobalTheory.EisM.sum_slz_repL_Vo | (intros; apply GlobalTheory.EisM.sum_slz_repL_Vo <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisenstein_latticeFunction_isModularFormCoeffSeq : ∀ (j L₁ L₂ : ℕ) (b χ₁ χ₂ : ℤ → ℂ) (φ : ZMod L₁ → ℂ), 1 ≤ j → 0 < L₁ → 0 < L₂ → hat φ 0 = 0 → (∀ x, b (x + L₂) = b x) → (∀ d : ℤ, IsCoprime d (L₁ * L₂ : ℕ) → (∀ y, φ y = χ₁ d * φ (y * d)) ∧ ∀ x, b (x * d) = χ₂ d * b x) → χ₁ (-1) * χ₂ (-1) = (-1) ^ j → ∃ c : ℂ, MF j (L₁ * L₂) (fun d => χ₁ d * χ₂ d) (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L₁ (0, 1) (latF L₁ b φ) τ = 2 * (-2 * π * Complex.I / L₁) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.EisForm.eis_latF_mf | exact GlobalTheory.EisForm.eis_latF_mf | (intros; apply GlobalTheory.EisForm.eis_latF_mf <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [twist, detChar, hd]
    rw [this]
  refine GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

theorem _root_.GlobalTheory.T.diamondMatrix_mul_comm_mod_gamma1CapGamma0 : ∀ (N l d d' : ℕ) (σ σ' : SL(2, ℤ)), IsDiam N l d σ → IsDiam N l d' σ' → ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  first | exact @GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | exact GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | (intros; apply GlobalTheory.KZ.isDiam_mul_comm_mod_Gam <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  first | exact @GlobalTheory.depletion_mf | exact GlobalTheory.depletion_mf | (intros; apply GlobalTheory.depletion_mf <;> assumption)
end
