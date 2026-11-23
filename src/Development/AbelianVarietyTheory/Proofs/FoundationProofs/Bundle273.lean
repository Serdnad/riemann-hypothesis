module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSigmaStarTranslatePowDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle267
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle268
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle269
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.InvariantDifferentialMulEqDerivX
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.SubstPairSubst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle265
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem rootOfUnity_eq_pow {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field K] [Algebra Ω K]
    (l : ℕ) (hl : 0 < l) (ζ : Kˣ) (hζ : ζ ^ l = 1) (m : ℕ) (hm : 0 < m) : ∃ η : Kˣ, ζ = η ^ m := by
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hω' : IsPrimitiveRoot (algebraMap Ω K ω) l := hω.map_of_injective (algebraMap Ω K).injective
  have hζK : (ζ : K) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one]
  obtain ⟨i, -, hi⟩ := hω'.eq_pow_of_pow_eq_one hζK
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ω ^ i) hm
  have hz0 : algebraMap Ω K z ≠ 0 := by
    intro h0
    have : (ζ : K) = 0 := by rw [← hi, ← map_pow, ← hz, map_pow, h0, zero_pow hm.ne']
    exact ζ.ne_zero this
  refine ⟨Units.mk0 _ hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hz, map_pow, hi]

theorem khat_no_l_torsion : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (x : X.Khat l), (l : ℤ_[l]) • x = 0 → x = 0 := by
  intro Ω _ _ _ ε X l _ x hx
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  suffices hn : ∀ n, AdicCompletion.eval (idl l) (X.Kl l) n x = 0 by
    apply AdicCompletion.ext
    intro n
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, hn, map_zero]
  intro n
  obtain ⟨hsurj, hker, hmul, hone, -, -, -⟩ := H3.cls_props Ω ε X l (n + 1)
  obtain ⟨-, hker0, -, hone0, -, -, hred⟩ := H3.cls_props Ω ε X l n
  obtain ⟨f, hf⟩ := hsurj (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x)
  have hpow : ∀ k : ℕ, X.cls l (n + 1) (f ^ k) = k • X.cls l (n + 1) f := by
    intro k
    induction k with
    | zero => simp [hone]
    | succ k ih => rw [pow_succ f k, hmul, ih, succ_nsmul]
  have h1 : X.cls l (n + 1) (f ^ l) = X.cls l (n + 1) 1 := by
    rw [hpow, hone, hf, ← Nat.cast_smul_eq_nsmul ℤ_[l], ← map_smul, hx, map_zero]
  obtain ⟨g, hg⟩ := (hker _ _).1 h1
  rw [one_mul] at hg
  set ζ : X.Kˣ := f * (g ^ (l ^ n))⁻¹ with hζdef
  have hζ : ζ ^ l = 1 := by
    rw [hζdef, mul_pow, hg, inv_pow, ← pow_mul, ← pow_succ, mul_inv_cancel]
  have : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨η, hη⟩ := rootOfUnity_eq_pow (Ω := Ω) l hl ζ hζ (l ^ n) (pow_pos hl n)
  have hf' : f = 1 * (η * g) ^ (l ^ n) := by
    rw [one_mul, mul_pow, ← hη, hζdef, inv_mul_cancel_right]
  rw [hred x f hf.symm, ← hone0]
  exact (hker0 _ _).2 ⟨_, hf'⟩

end GlobalTheory.KZ.BettiB
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

theorem _root_.GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  first | exact @GlobalTheory.ThetaTranslDecomp.exists_decomp | exact GlobalTheory.ThetaTranslDecomp.exists_decomp | (intros; apply GlobalTheory.ThetaTranslDecomp.exists_decomp <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobeniusStickelberger_defect_subst_formal_group_log : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.FrobStick.SubstLog.subst_log_formula | exact GlobalTheory.FrobStick.SubstLog.subst_log_formula | (intros; apply GlobalTheory.FrobStick.SubstLog.subst_log_formula <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobeniusStickelbergerDeterminantDefect_on_line : ∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  first | exact @GlobalTheory.FrobStick.defect_line | exact GlobalTheory.FrobStick.defect_line | (intros; apply GlobalTheory.FrobStick.defect_line <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobenius_stickelberger_sigmaStar_det_complex : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  first | exact @GlobalTheory.FrobStick.sgStar_cube_det_cplx | exact GlobalTheory.FrobStick.sgStar_cube_det_cplx | (intros; apply GlobalTheory.FrobStick.sgStar_cube_det_cplx <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.frobeniusStickelberger_taylor_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  first | exact @GlobalTheory.FrobStick.tay_defect_eq_zero | exact GlobalTheory.FrobStick.tay_defect_eq_zero | (intros; apply GlobalTheory.FrobStick.tay_defect_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open scoped TensorProduct Matrix

namespace GlobalTheory.GenusCong

open GlobalTheory.NormSum.RepAt

theorem mem_iff_one_add {R : Type} [CommRing R] (O : Subring R) {n : ℕ} (L : Submodule O (Fin n → R))
    (m : R) (hmO : m ∈ O)
    (hm : ∀ Y ∈ matIn O n, ∀ u ∈ L, m • (Y *ᵥ u) ∈ L)
    (a : O) (ha : ∀ x : O, IsUnit (1 + a * x))
    (X : Matrix (Fin n) (Fin n) R) (hX : X ∈ matIn O n) (w : Fin n → R) :
    w ∈ L ↔ (1 + (a : R) • m • X) *ᵥ w ∈ L := by
  have haX : (a : R) • X ∈ matIn O n := fun i j => mul_mem a.2 (hX i j)
  constructor
  · intro hw
    rw [Matrix.add_mulVec, Matrix.one_mulVec, smul_comm, Matrix.smul_mulVec]
    exact add_mem hw (hm _ haX _ hw)
  · intro hz
    obtain ⟨W, hW, e⟩ := mat_inv O a ha (m • X) (fun i j => mul_mem hmO (hX i j))
    have e' := mul_eq_one_comm.1 e
    have eW : W = 1 - m • ((a : R) • X * W) := by
      rw [← e, add_mul, one_mul, smul_comm, Matrix.smul_mul, add_sub_cancel_right]
    have h1 : w = W *ᵥ ((1 + (a : R) • m • X) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
    generalize (1 + (a : R) • m • X) *ᵥ w = z at hz h1
    rw [h1, eW, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    exact sub_mem hz (hm _ (mul_mem haX hW) _ hz)

theorem eps_mulVec {R : Type} [CommRing R] {n : ℕ} (e p m : R) (he : e * e = e)
    (k X : Matrix (Fin n) (Fin n) R) (h : e • (k - 1) = (p * m) • X) (u : Fin n → R) :
    e • (k *ᵥ u) = (1 + (e * p) • m • X) *ᵥ (e • u) := by
  have h1 : e • k = e • (1 + (e * p) • m • X) := by
    rw [smul_add, smul_smul, smul_smul, ← mul_assoc, he, mul_assoc, mul_smul, ← h, smul_smul, he,
      smul_sub, add_sub_cancel]
  rw [← Matrix.smul_mulVec, h1, Matrix.smul_mulVec, Matrix.mulVec_smul]

section Ad

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] 𝔸
local notation "𝒮" => tensInt (F := F) 𝔸 (intOE E) (intAd F)

theorem exists_mult {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ m : ℕ, 0 < m ∧ ∀ Y ∈ matIn 𝒮 n, ∀ u ∈ latS (F := F) 𝔸 𝒮 Λ,
      (m : 𝒜) • (Y *ᵥ u) ∈ latS (F := F) 𝔸 𝒮 Λ := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c₁ * c₂}))
  have hcast (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : 𝒜) := by
    rw [levelafC, map_natCast]
    exact map_natCast (Algebra.TensorProduct.includeRight : 𝔸 →ₐ[F] 𝒜) m
  refine ⟨Ideal.absNorm (Ideal.span {c₁ * c₂}), Nat.pos_of_ne_zero ?_, fun Y hY u hu => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc₁ hc₂
  · rw [← hcast, ← hc, levelafC_mul, levelafC_mul]
    have e : (levelafC E c * (levelafC E c₁ * levelafC E c₂)) • (Y *ᵥ u) =
        fun i => levelafC E c₁ * ∑ j, levelafC E c * Y i j * (levelafC E c₂ * u j) := by
      ext i
      rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact h₁ _ fun i => sum_mem fun j _ => mul_mem (mul_mem (levelafC_mem c) (hY i j)) (h₂ u hu j)

end Ad

theorem eps_mem_latS_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∃ D : ℕ, 0 < D ∧ ∀ (k X : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)), (∀ i j, X i j ∈ tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) → afsplitEps E v • (k - 1) = D • X → ∀ u : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, afsplitEps E v • u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ afsplitEps E v • (k *ᵥ u) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ := by
  intro F E _ _ _ _ _ n Λ hfin hspan v
  obtain ⟨m, hm0, hm⟩ := exists_mult (F := F) Λ hfin hspan
  have hpv := Ideal.absNorm_mem v.asIdeal
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal = p at hpv hp
  refine ⟨p * m, Nat.mul_pos hp hm0, fun k X hX h u => ?_⟩
  rw [← Nat.cast_smul_eq_nsmul (E ⊗[F] FiniteAdeleRing (𝓞 F) F), Nat.cast_mul] at h
  have heps : afsplitEps E v * (p : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      (1 : E) ⊗ₜ[F] afsplitI v p := by
    rw [← afsplit_decomp, map_natCast, ← afsplitIE_tmul]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight :
      v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F) p).symm
  rw [eps_mulVec _ _ _ (afsplit_eps_idem v) k X h u, heps]
  let a : intAd F := ⟨afsplitI v p, afsplitI_mem_intAd v _ (natCast_mem _ _)⟩
  have hcastVal : Valued.v (p : v.adicCompletion F) = v.valuation F (algebraMap (𝓞 F) F p) := by
    rw [← levelaf_valued_algebraMap, map_natCast (algebraMap (𝓞 F) F), map_natCast (algebraMap F _)]
  have ha (c : intAd F) : IsUnit (1 + a * c) := by
    have hval : Valued.v (1 + (p : v.adicCompletion F) * (c : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
      apply Valuation.map_one_add_of_lt
      rw [Valuation.map_mul, hcastVal]
      exact mul_lt_one_of_lt_of_le ((v.valuation_lt_one_iff_mem _).2 hpv)
        ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (c.2 v))
    have hne : 1 + (p : v.adicCompletion F) * (c : FiniteAdeleRing (𝓞 F) F) v ≠ 0 := fun hzero => by
      rw [hzero, map_zero] at hval
      exact zero_ne_one hval
    refine IsUnit.of_mul_eq_one ⟨1 - afsplitI v 1 +
      afsplitI v (1 + (p : v.adicCompletion F) * (c : FiniteAdeleRing (𝓞 F) F) v)⁻¹,
      add_mem (sub_mem (one_mem _) (afsplitI_mem_intAd v _ (one_mem _))) (afsplitI_mem_intAd v _ ?_)⟩ ?_
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
    · apply Subtype.ext
      change (1 + afsplitI v p * (c : FiniteAdeleRing (𝓞 F) F)) * _ = 1
      ext w
      by_cases hw : w = v
      · subst w
        simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_self,
          sub_self, zero_add, mul_inv_cancel₀ hne]
      · simp only [afsplit_add_apply, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply, afsplitI_ne v w hw,
          zero_mul, add_zero, sub_zero, mul_one]
  let S := tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
  let incl : FiniteAdeleRing (𝓞 F) F →ₐ[F] E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
    Algebra.TensorProduct.includeRight
  let ι : intAd F →+* S := (incl.toRingHom.comp (intAd F).subtype).codRestrict _
    fun y => Subring.subset_closure (Or.inr ⟨y, rfl⟩)
  have hIntegral : ι.IsIntegral := by
    rintro ⟨x, hx⟩
    refine Subring.closure_induction
      (p := fun x hx => ι.IsIntegralElem ⟨x, hx⟩) ?_ ?_ ?_ ?_ ?_ ?_ hx
    · rintro x (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
      · let ψ : 𝓞 E →+* S :=
          ((inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap (𝓞 E) E)).codRestrict _
            fun y => Subring.subset_closure (Or.inl ⟨⟨_, ⟨y, rfl⟩⟩, rfl⟩)
        have hb : IsIntegral ℤ (ψ b) := map_isIntegral_int ψ (Algebra.IsIntegral.isIntegral b)
        let := ι.toAlgebra
        exact hb.tower_top (A := intAd F)
      · exact RingHom.isIntegralElem_map ι (x := y)
    · exact RingHom.isIntegralElem_zero _
    · exact RingHom.isIntegralElem_one _
    · intro x y _ _ hx hy; exact hx.add _ hy
    · intro x _ hx; exact hx.neg _
    · intro x y _ _ hx hy; exact hx.mul _ hy
  exact mem_iff_one_add _ _ _ (natCast_mem _ _) hm (ι a) (unit_of_integral ι hIntegral a ha) X hX _

end GlobalTheory.GenusCong
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaLattice_triples_distributive : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  first | exact @GlobalTheory.DistLa.dist_La | exact GlobalTheory.DistLa.dist_La | (intros; apply GlobalTheory.DistLa.dist_La <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTripleConstant_eq_cocycle_sum : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  first | exact @GlobalTheory.TripleConstant.mu_form | exact GlobalTheory.TripleConstant.mu_form | (intros; apply GlobalTheory.TripleConstant.mu_form <;> assumption)
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

theorem _root_.GlobalTheory.T.zeta_sub_one_mem_span_galois_differences : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ j : ℕ, 1 ≤ j → ∀ g ∈ Hinf T, g r ≠ r →
  T.ζ j - 1 ∈ Submodule.span (FixI (Hfix T r)) {y : Ω | ∃ x ∈ FixI (Hfix T r), y = g x - x} := by
  first | exact @GlobalTheory.KumIdeal.zeta_sub_one_mem_span | exact GlobalTheory.KumIdeal.zeta_sub_one_mem_span | (intros; apply GlobalTheory.KumIdeal.zeta_sub_one_mem_span <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.muModelProduct_isModularFormCoeffSeq_locallyAlgebraic : ∀ (k j N l m : ℕ) (ε : DirichletCharacter ℂ N) (u : ℤ → ℂ) (θ ν : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ (l ^ m)), j + 2 ≤ k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → (∀ x, u (x + N) = u x) → (∀ d x : ℤ, IsCoprime d N → u (x * d) = ch θ⁻¹ d * u x) → ε = θ⁻¹ * ν → ψ (-1) * θ (-1) = (-1) ^ (k - 1 - j) → ψ (-1) * ν (-1) = (-1) ^ (j + 1) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l u (ch ν) (fun x y => ch ψ x * ch ψ⁻¹ y * ((y : ℂ) / x) ^ j)) := by
  first | exact @GlobalTheory.zm_char_mf | exact GlobalTheory.zm_char_mf | (intros; apply GlobalTheory.zm_char_mf <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.IntDLog

open PowerSeries Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

def intModel (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    WeierstrassCurve (Formalism.G.unitBall ℂ_[p]) :=
  ⟨⟨g.W.a₁, h.1⟩, ⟨g.W.a₂, h.2.1⟩, ⟨g.W.a₃, h.2.2.1⟩, ⟨g.W.a₄, h.2.2.2.1⟩, ⟨g.W.a₆, h.2.2.2.2⟩⟩

theorem intModel_map (g : G1 p) (h : Formalism.L2.Th1.A.IntModel g.W) :
    (intModel g h).map (Formalism.G.unitBall ℂ_[p]).subtype = g.W := by
  ext <;> rfl

theorem subst_mul_log_eq_nSer (g : G1 p) (hOk : g.Ok) (N : ℕ) :
    (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p]) =
      Formalism.L2.Th1.A.nSer g.W N := by
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  obtain ⟨hl0, -, -, -⟩ := Formalism.L2.Th1.A.logSpec ℂ_[p] g.W
  obtain ⟨he0, -, hLE, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  induction N with
  | zero =>
    simp only [Nat.cast_zero, map_zero, zero_mul]
    rw [he]
    exact PowerSeries.subst_zero_of_constantCoeff_zero he0
  | succ N ih =>
    have hcN : PowerSeries.constantCoeff (Formalism.L2.Th1.A.nSer g.W N) = 0 :=
      Formalism.L2.Th1.A.ZSer.nSer_cc g.W N
    have hadd := Formalism.L2.KerInert.Dict.formal_addition_agree p g hOk Unit
      (PowerSeries.X : MvPowerSeries Unit ℂ_[p]) (Formalism.L2.Th1.A.nSer g.W N) (MvPowerSeries.constantCoeff_X _) hcN
    have hN : PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l = PowerSeries.C (N : ℂ_[p]) * g.l := by
      have hb : HasSubst (PowerSeries.C (N : ℂ_[p]) * g.l) :=
        HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl, hl0, mul_zero])
      have hex : HasSubst g.ex := HasSubst.of_constantCoeff_zero' (by rw [he]; exact he0)
      have hLE' : PowerSeries.subst g.ex g.l = PowerSeries.X := by rw [he, hl]; exact hLE
      rw [← ih, ← PowerSeries.subst_comp_subst_apply hex hb g.l, hLE', PowerSeries.subst_X hb]
    show _ = MvPowerSeries.subst (![PowerSeries.X, Formalism.L2.Th1.A.nSer g.W N] : Fin 2 → PowerSeries ℂ_[p])
      (Formalism.L2.Th1.A.fgl g.W)
    rw [← hadd]
    show _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.l +
      PowerSeries.subst (Formalism.L2.Th1.A.nSer g.W N) g.l) g.ex
    rw [hN, PowerSeries.X_subst]
    congr 1
    push_cast
    rw [map_add (f := _), map_one]
    ring

theorem int_dlog : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → (∀ (f : PowerSeries ℂ_[p]), (∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) → ∀ n : ℕ, ‖(n.factorial : ℂ_[p]) * PowerSeries.coeff n (PowerSeries.subst g.ex f : PowerSeries ℂ_[p])‖ ≤ 1) ∧ (PowerSeries.subst g.l g.ex : PowerSeries ℂ_[p]) = PowerSeries.X ∧ ∀ N : ℕ, ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst (PowerSeries.C (N : ℂ_[p]) * g.l) g.ex : PowerSeries ℂ_[p])‖ ≤ 1 := by
  intro p _ g hOk
  have hl : g.l = Formalism.L2.Th1.A.logSer g.W :=
    Formalism.L2.KerInert.Dict.formal_logarithm_agree p g.W g.wq hOk.2.1
  have he : g.ex = Formalism.L2.Th1.A.expSer g.W := Formalism.L2.KerInert.Dict.formal_exponential_agree p g hOk
  have hM := Formalism.L2.KerInert.Dict.intModel_of_ok hOk
  obtain ⟨-, -, -, hEL, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] g.W
  refine ⟨?_, ?_, ?_⟩
  · intro f hf n
    have hJ := (Formalism.L2.Th1.A.jetMem ℂ_[p] g.W (Formalism.G.unitBall ℂ_[p]) hM.1 hM.2.1 hM.2.2.1
      hM.2.2.2.1 hM.2.2.2.2).2.1 f hf n
    rw [he]
    exact hJ
  · rw [hl, he]
    exact hEL
  · intro N n
    rw [subst_mul_log_eq_nSer g hOk N, ← intModel_map g hM]
    have hz := GlobalTheory.WeierstrassFormal.map_zsmul (intModel g hM) (Formalism.G.unitBall ℂ_[p]).subtype (N : ℤ)
    change PowerSeries.map _ (Formalism.L2.Th1.A.nSer _ N) = Formalism.L2.Th1.A.nSer _ N at hz
    rw [← hz, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (Formalism.L2.Th1.A.nSer (intModel g hM) N)).2

end GlobalTheory.IntDLog

end
end
