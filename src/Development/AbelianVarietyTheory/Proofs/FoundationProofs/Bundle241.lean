module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle188
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle206
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle179
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle233
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.fock_intertwiner_commutes_unitary_and_extends : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  first | exact @GlobalTheory.FockExtGroup.comm_and_extend | exact GlobalTheory.FockExtGroup.comm_and_extend | (intros; apply GlobalTheory.FockExtGroup.comm_and_extend <;> assumption)
end

section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harmonic_highestWeight_eq_lowestKTypeHighestWeight : ∀ (p q n : ℕ) (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (μ : Ix p q → ℚ) (P : Pol p q n 0), IsHW (fockAct1 p q n 0) μ P → P ∈ hwSub (fockAct2 p q n 0) (wtH n ap am) → KilledByLower (fockAct1 p q n 0) P → μ = wtK n ap am := by
  first | exact @GlobalTheory.HarmonicShape.weight_eq_wtK | exact GlobalTheory.HarmonicShape.weight_eq_wtK | (intros; apply GlobalTheory.HarmonicShape.weight_eq_wtK <;> assumption)
end

section

open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm


open GlobalTheory.NormSum.MovedLattice in
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add (f := _), add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex

end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.shimuraReciprocity_conjugate_form_level : ∀ (g : ℂ ≃+* ℂ) (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) (k : ℕ) (f : ℍ → ℂ), ZetaAct g N d → Even k → (∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[(k : ℤ)] γ = f) → (∀ γ : SL(2, ℤ), ∃ a, HasQ N (f ∣[(k : ℤ)] γ) a) → ∃ f' : ℍ → ℂ, (∀ γ ∈ CongruenceSubgroup.Gamma N, f' ∣[(k : ℤ)] γ = f') ∧ ∀ γ γ' : SL(2, ℤ), dg d * redGL N γ' = redGL N γ * dg d → QConj g N (f ∣[(k : ℤ)] γ) (f' ∣[(k : ℤ)] γ') := by
  first | exact @GlobalTheory.FNConj.main | exact GlobalTheory.FNConj.main | (intros; apply GlobalTheory.FNConj.main <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  first | exact @GlobalTheory.EisAL.atkin_lehner_eis | exact GlobalTheory.EisAL.atkin_lehner_eis | (intros; apply GlobalTheory.EisAL.atkin_lehner_eis <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem petInt_mp (γ : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have h := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  convert h using 1
  ext z
  simp

theorem petInt_emb (γ : SL(2, ℤ)) : MeasurableEmbedding (fun z : ℍ => γ • z) := by
  have h := measurableEmbedding_const_smul (α := ℍ) ((γ : GL (Fin 2) ℝ))
  convert h using 1
  ext z
  simp

theorem petInt_fd_meas : MeasurableSet ModularGroup.fd := by
  unfold ModularGroup.fd
  apply IsClosed.measurableSet
  change IsClosed ({z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} ∩ {z : ℍ | |z.re| ≤ 1 / 2})
  apply IsClosed.inter
  · exact isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  · exact isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const

theorem petInt_im_bd (γ : SL(2, ℤ)) (σ : ℍ) (hσ : σ ∈ ModularGroup.fd) :
    (γ • σ).im ≤ 2 * σ.im ∧
      ((γ • σ).im)⁻¹ ≤ (3 * ((γ 1 0 : ℤ) : ℝ) ^ 2 + 8 * ((γ 1 1 : ℤ) : ℝ) ^ 2) * σ.im := by
  have hy : 3 ≤ 4 * σ.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
  have hx : |σ.re| ≤ 1 / 2 := hσ.2
  have hyp : 0 < σ.im := σ.im_pos
  have hx2 : σ.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg σ.re, sq_abs σ.re]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hcd : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 ∨ (((γ 1 0 : ℤ) : ℝ) = 0 ∧ ((γ 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
    by_cases h0 : (γ 1 0 : ℤ) = 0
    · right
      rw [h0, mul_zero, sub_zero, mul_comm] at hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;>
        simp [h0, h]
    · left
      have h1 : (1 : ℤ) ≤ (γ 1 0 : ℤ) ^ 2 := by
        rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
      exact_mod_cast h1
  have hN : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) σ) =
      (((γ 1 0 : ℤ) : ℝ) * σ.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 + (((γ 1 0 : ℤ) : ℝ) * σ.im) ^ 2 := by
    rw [ModularGroup.denom_apply]
    simp [Complex.normSq_apply]
    ring
  rw [ModularGroup.im_smul_eq_div_normSq, hN]
  generalize ((γ 1 0 : ℤ) : ℝ) = c at *
  generalize ((γ 1 1 : ℤ) : ℝ) = d at *
  have hhalf : 1 / 2 ≤ (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by
    rcases hcd with h | ⟨hc, hd⟩
    · nlinarith [sq_nonneg (c * σ.re + d), mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ c ^ 2)]
    · subst hc
      nlinarith
  have hNpos : 0 < (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by linarith
  constructor
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [inv_div, div_le_iff₀ hyp]
    nlinarith [sq_nonneg (c * σ.re - d), mul_le_mul_of_nonneg_left hx2 (sq_nonneg c),
      mul_le_mul_of_nonneg_left hy (sq_nonneg c), mul_le_mul_of_nonneg_left hy (sq_nonneg d)]

theorem petInt_real (k A : ℕ) (r q f t y C C' K δ : ℝ) (hr1 : r ≤ 1) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (ht : 0 < t) (ht1 : t ≤ 2 * y) (ht2 : t⁻¹ ≤ K * y)
    (hdec : q ^ 2 * t ^ k ≤ C * Real.exp (-δ * y)) (hF : f ≤ C' * (t ^ A + (t ^ A)⁻¹)) :
    r * (q * f * t ^ k) ≤ C / 2 * (y ^ 0 * Real.exp (-(δ / 2) * y)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (y ^ (2 * A + k) * Real.exp (-(δ / 2) * y)) := by
  have hy : 0 < y := by linarith
  have hKy : 0 < K * y := lt_of_lt_of_le (inv_pos.mpr ht) ht2
  set E := Real.exp (-(δ / 2) * y) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-δ * y) = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have htk : 0 < t ^ k := pow_pos ht k
  have hS : t ^ A + (t ^ A)⁻¹ ≤ (2 ^ A + K ^ A) * y ^ A := by
    have h1 : t ^ A ≤ (2 * y) ^ A := pow_le_pow_left₀ ht.le ht1 A
    have h2 : (t ^ A)⁻¹ ≤ (K * y) ^ A := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ht2 A
    rw [mul_pow] at h1 h2
    linarith
  have hSpos : 0 ≤ t ^ A + (t ^ A)⁻¹ := by positivity
  have hf' : f ≤ |C'| * ((2 ^ A + K ^ A) * y ^ A) :=
    le_trans hF (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C') hSpos)
      (mul_le_mul_of_nonneg_left hS (abs_nonneg _)))
  have hf2 : f ^ 2 ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
    calc f ^ 2 ≤ (|C'| * ((2 ^ A + K ^ A) * y ^ A)) ^ 2 := pow_le_pow_left₀ hf hf' 2
      _ = (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
        rw [mul_comm 2 A, pow_mul]
        ring
  have htk2 : t ^ k ≤ 2 ^ k * y ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le ht1 k
  have key : 2 * (q * f * t ^ k) * E ≤ (C * E + f ^ 2 * t ^ k * E) * E := by
    rw [hE2] at hdec
    nlinarith [mul_nonneg (sq_nonneg (q - f * E)) htk.le]
  have key2 : 2 * (q * f * t ^ k) ≤ C * E + f ^ 2 * t ^ k * E := le_of_mul_le_mul_right key hEpos
  have hft : f ^ 2 * t ^ k ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) * (2 ^ k * y ^ k) :=
    mul_le_mul hf2 htk2 htk.le (by positivity)
  have hP : 0 ≤ q * f * t ^ k := by positivity
  refine le_trans (mul_le_of_le_one_left hP hr1) ?_
  rw [pow_zero, one_mul, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hft hEpos.le]

theorem integrable_pet_integrand : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  intro k L L' N ε a ρ F hk hL' hN hW hCF hFm hMod
  set g : ℍ → ℂ := fun τ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k) with hg
  have hρ1 : ∀ τ, ρ τ ≤ 1 := by
    intro τ
    have h := le_hasSum (hW.sum τ) 1 (fun j _ => hW.nonneg _)
    simpa using h
  have hqc : Continuous (qs a) := (qs_summable_continuous a hCF.1.1).2
  have hgm : AEStronglyMeasurable g volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hW.meas).aestronglyMeasurable
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hFm) ?_
      · exact (Complex.continuous_conj.comp hqc).aestronglyMeasurable
      · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow k).aestronglyMeasurable
  obtain ⟨S, hS⟩ := hW.supp
  obtain ⟨C', A, hC'⟩ := hMod
  have hsupp : Function.support g ⊆ ⋃ γ ∈ S, {τ : ℍ | γ • τ ∈ ModularGroup.fd} := by
    intro τ hτ
    have hρ : ρ τ ≠ 0 := by
      intro h0
      apply hτ
      simp [hg, h0]
    obtain ⟨γ, hγS, hγ⟩ := hS τ hρ
    exact Set.mem_biUnion hγS hγ
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, integrableOn_finset_iUnion]
  intro γ hγS
  have hpre : (fun σ : ℍ => γ⁻¹ • σ) ⁻¹' {τ : ℍ | γ • τ ∈ ModularGroup.fd} = ModularGroup.fd := by
    ext σ
    simp
  rw [← (petInt_mp γ⁻¹).integrableOn_comp_preimage (petInt_emb γ⁻¹), hpre]
  obtain ⟨C, δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L' N ε a γ⁻¹ hk hL' hN hCF
  set K : ℝ := 3 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 + 8 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℝ) ^ 2 with hK
  refine Integrable.mono' (g := fun σ : ℍ => C / 2 * (σ.im ^ 0 * Real.exp (-(δ / 2) * σ.im)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (σ.im ^ (2 * A + k) * Real.exp (-(δ / 2) * σ.im))) ?_ ?_ ?_
  · exact ((integrableOn_fd_im_pow_mul_exp (δ / 2) 0 (by positivity)).const_mul _).add
      ((integrableOn_fd_im_pow_mul_exp (δ / 2) (2 * A + k) (by positivity)).const_mul _)
  · exact (hgm.comp_measurePreserving (petInt_mp γ⁻¹)).restrict
  · refine (ae_restrict_iff' petInt_fd_meas).mpr (Filter.Eventually.of_forall fun σ hσ => ?_)
    have hy : 1 / 2 ≤ σ.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
      nlinarith [σ.im_pos]
    obtain ⟨hb1, hb2⟩ := petInt_im_bd γ⁻¹ σ hσ
    have ht := (γ⁻¹ • σ).im_pos
    have hn : ‖g (γ⁻¹ • σ)‖ = ρ (γ⁻¹ • σ) * (‖qs a (γ⁻¹ • σ)‖ * ‖F (γ⁻¹ • σ)‖ * (γ⁻¹ • σ).im ^ k) := by
      simp only [hg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
        abs_of_nonneg (hW.nonneg _), abs_of_pos ht]
    rw [Function.comp_apply, hn]
    exact petInt_real k A _ _ _ _ σ.im C C' K δ (hρ1 _) (norm_nonneg _) (norm_nonneg _) ht hb1 hb2
      (hdec σ hy) (hC' _)

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.jacquetKernel_eigenvector_eq_zero_of_const_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_isEig_const | exact GlobalTheory.PsType.eq_zero_of_isEig_const | (intros; apply GlobalTheory.PsType.eq_zero_of_isEig_const <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.exists_strip_clearing_upperRight_principalSeriesCongruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k), Ordered ψ → Cut ψ r → ∀ j ∈ grp ψ, ∃ y ∈ strip ψ r ϖ 0, ∀ a b : Fin n, (a : ℕ) < r → r ≤ (b : ℕ) → (y⁻¹ * j).val a b = 0 := by
  first | exact @GlobalTheory.PsType.clear_upper_right | exact GlobalTheory.PsType.clear_upper_right | (intros; apply GlobalTheory.PsType.clear_upper_right <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_lam_eq_and_vanishes_off_character : ∀ (k L N : ℕ) (χ₀ : DirichletCharacter ℂ N) (B : ℕ) (c : ℕ → ℂ), 0 < L → N ∣ L → ∃ (B' : ℕ) (c' : ℕ → ℂ), (∀ a, MF k L (ch χ₀) a → lam B' c' a = lam B c a) ∧ ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ₀ → MF k L (ch ε) a → lam B' c' a = 0 := by
  first | exact @GlobalTheory.lam_extend_by_zero | exact GlobalTheory.lam_extend_by_zero | (intros; apply GlobalTheory.lam_extend_by_zero <;> assumption)
end

section

open GlobalTheory.DualWeyl MvPolynomial NumberField

theorem _root_.GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (la : Fin N → ℕ), Antitone la → ∀ f ∈ nabla la K, IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.rowW N N) f la → f = evalAt 1 f • extremal la K := by
  first | exact @GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | exact GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight | (intros; apply GlobalTheory.DualWeyl.eq_evalAt_one_smul_extremal_of_rowWeight <;> assumption)
end
