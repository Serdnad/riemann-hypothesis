module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ResAlgOfTheta
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QSplitHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def hd {a : ℕ} (i : Fin a) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i i 1, fun p q => by
    rw [Matrix.single_apply, Matrix.single_apply, apply_ite (sigR (Fv F v) σ), map_one, map_zero]
    exact if_congr and_comm rfl rfl⟩

theorem hm_apply_ne {a : ℕ} (hinv : ∀ y, σ (σ y) = y) {k l i j : Fin a} (c : Fv F v ⊗[F] E)
    (h1 : ¬(k = i ∧ l = j)) (h2 : ¬(l = i ∧ k = j)) :
    (hm σ v hinv k l c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show (Matrix.single k l c + Matrix.single l k (sigR (Fv F v) σ c)) i j = 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]

theorem hd_apply_ne {a : ℕ} {k i j : Fin a} (h : ¬(k = i ∧ k = j)) :
    (hd σ v k : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show Matrix.single k k (1 : Fv F v ⊗[F] E) i j = 0
  rw [Matrix.single_apply, if_neg h]

def hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (p : Fin a × Fin a) : HermR (Fv F v) σ a :=
  if p.1 < p.2 then hm σ v hinv p.1 p.2 (β 0) else if p.2 < p.1 then hm σ v hinv p.2 p.1 (β 1) else hd σ v p.1

theorem hb_zero {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {p : Fin a × Fin a} {i j : Fin a}
    (hp1 : p ≠ (i, j)) (hp2 : p ≠ (j, i)) : (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  obtain ⟨k, l⟩ := p
  unfold hb
  dsimp only
  split_ifs with hkl hlk
  · exact hm_apply_ne σ v hinv _ (fun e => hp1 (Prod.ext e.1 e.2)) (fun e => hp2 (Prod.ext e.2 e.1))
  · exact hm_apply_ne σ v hinv _ (fun e => hp2 (Prod.ext e.2 e.1)) (fun e => hp1 (Prod.ext e.1 e.2))
  · have hkl' : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
    subst hkl'
    exact hd_apply_ne σ v (fun e => hp1 (Prod.ext e.1 e.2))

theorem hermitian_basis_above_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 0 := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single i j (β 0) + Matrix.single j i (sigR (Fv F v) σ (β 0))) i j = β 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_above_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 1 := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single i j (β 1) + Matrix.single j i (sigR (Fv F v) σ (β 1))) i j = β 1
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_below_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 1) := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single j i (β 1) + Matrix.single i j (sigR (Fv F v) σ (β 1))) i j = sigR (Fv F v) σ (β 1)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hermitian_basis_below_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 0) := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single j i (β 0) + Matrix.single i j (sigR (Fv F v) σ (β 0))) i j = sigR (Fv F v) σ (β 0)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hb_eq {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (i : Fin a) :
    (hb σ v hinv β (i, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i = 1 := by
  unfold hb
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  show Matrix.single i i (1 : Fv F v ⊗[F] E) i i = 1
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

theorem coe_sum_hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i j : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      ∑ p, c p • (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
  rfl

theorem sum_lt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : i < j) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • β 0 + c (j, i) • β 1 := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_above_first σ v hinv β h, hermitian_basis_above_second σ v hinv β h]

theorem sum_gt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : j < i) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • sigR (Fv F v) σ (β 1) + c (j, i) • sigR (Fv F v) σ (β 0) := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne' (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_below_first σ v hinv β h, hermitian_basis_below_second σ v hinv β h]

theorem sum_diag {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i =
      sc (E := E) v (c (i, i)) := by
  rw [coe_sum_hb, Fintype.sum_eq_single (i, i) (fun p hp => by rw [hb_zero σ v hinv β hp hp, smul_zero]),
    hb_eq, sc, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PI.OmLocU.SdB
end
end

section

noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

set_option linter.deprecated false

def ThetaSpan : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ θ : 𝓞 E,
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) →
    ∀ x ∈ OEv (E := E) v, ∃ a0 a1 : v.adicCompletionIntegers F,
      x = sc (E := E) v (a0 : Fv F v) + sc (E := E) v (a1 : Fv F v) * inclR (F := F) (Fv F v) (θ : E)

theorem theta_exists (h : IsCMExt F E σ) : ∃ θ : 𝓞 E,
    (∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) ∧
    (∀ q : QE (E := E) v, ∃ a0 a1 : 𝓞 F ⧸ v.asIdeal,
      q = algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 * Ideal.Quotient.mk (IE (E := E) v) θ) := by
  classical
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := finite_res v
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hcard : Nat.card (QE (E := E) v) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ 2 := card_QE σ v h
  have hk : 1 < Nat.card (𝓞 F ⧸ v.asIdeal) := Finite.one_lt_card
  have hpos : Nat.card (QE (E := E) v) ≠ 0 := by
    rw [hcard]
    positivity
  haveI : Finite (QE (E := E) v) := Nat.finite_of_card_ne_zero hpos
  haveI : Nontrivial (QE (E := E) v) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    nlinarith
  have hx : ∃ x : QE (E := E) v, x ∉ Set.range (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := by
    by_contra hne
    push_neg at hne
    have hs : Function.Surjective (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)) := fun y => hne y
    have hle := Nat.card_le_card_of_surjective _ hs
    rw [hcard] at hle
    nlinarith
  obtain ⟨x, hx⟩ := hx
  obtain ⟨θ, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hind : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0 := by
    intro a0 a1 h0
    by_cases ha1 : a1 = 0
    · subst ha1
      simp only [map_zero, zero_mul, add_zero] at h0
      exact ⟨(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v)).injective (by rw [h0, map_zero]), rfl⟩
    · exfalso
      apply hx
      refine ⟨-(a0 * a1⁻¹), ?_⟩
      have hinv : algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹ *
          algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1 = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ha1, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) a1⁻¹)) * h0 +
        (Ideal.Quotient.mk (IE (E := E) v) θ) * hinv
  refine ⟨θ, hind, ?_⟩
  let f : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) → QE (E := E) v := fun p =>
    algebraMap _ (QE (E := E) v) p.1 + algebraMap _ (QE (E := E) v) p.2 * Ideal.Quotient.mk (IE (E := E) v) θ
  have hinj : Function.Injective f := by
    intro p p' hpp
    have h0 := hind (p.1 - p'.1) (p.2 - p'.2) (by
      simp only [f] at hpp
      rw [map_sub, map_sub]
      linear_combination hpp)
    exact Prod.ext (sub_eq_zero.mp h0.1) (sub_eq_zero.mp h0.2)
  have hbij := bij_of_card f hinj (by rw [Nat.card_prod, hcard, sq])
  intro q
  obtain ⟨p, hp⟩ := hbij.2 q
  exact ⟨p.1, p.2, hp.symm⟩

theorem theta_indep (h : IsCMExt F E σ) (θ : 𝓞 E)
    (h3 : ∀ a0 a1 : 𝓞 F ⧸ v.asIdeal, algebraMap _ (QE (E := E) v) a0 + algebraMap _ (QE (E := E) v) a1 *
      Ideal.Quotient.mk (IE (E := E) v) θ = 0 → a0 = 0 ∧ a1 = 0) :
    ∀ a0 a1 : Fv F v, sc (E := E) v a0 + sc (E := E) v a1 * inclR (F := F) (Fv F v) (θ : E) = 0 →
      a0 = 0 ∧ a1 = 0 := by
  classical
  intro a0 a1 h0
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hθ : ∀ f : F, algebraMap F E f ≠ (θ : E) := by
    intro f hf
    have hint : IsIntegral ℤ f := (isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom)
        (algebraMap F E).injective).mp (by
      show IsIntegral ℤ (algebraMap F E f)
      rw [hf]
      exact RingOfIntegers.isIntegral_coe θ)
    have hg : θ = algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩ := by
      apply RingOfIntegers.ext
      rw [← hf]
      rfl
    have hz := h3 (-(Ideal.Quotient.mk _ ⟨f, hint⟩)) 1 (by
      rw [map_neg, map_one, one_mul, hg]
      show -Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) +
        Ideal.Quotient.mk (IE (E := E) v) (algebraMap (𝓞 F) (𝓞 E) ⟨f, hint⟩) = 0
      exact neg_add_cancel _)
    exact one_ne_zero hz.2
  have hli : LinearIndependent F ![(1 : E), (θ : E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
      exact ⟨(algebraMap F E).injective (by rw [hst, map_zero]), rfl⟩
    · exfalso
      apply hθ (-(s * t⁻¹))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have hinv : algebraMap F E t⁻¹ * algebraMap F E t = 1 := by
        rw [← map_mul, inv_mul_cancel₀ ht, map_one]
      rw [map_neg, map_mul]
      linear_combination (-(algebraMap F E t⁻¹)) * hst + (θ : E) * hinv
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, h.2.2.1])
  let b' := Algebra.TensorProduct.basis (Fv F v) b
  have hb : ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] = ⇑b' := by
    ext i
    fin_cases i <;>
      simp [b', b, Algebra.TensorProduct.basis_apply, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hli' : LinearIndependent (Fv F v) ![(1 : Fv F v) ⊗ₜ[F] (1 : E), (1 : Fv F v) ⊗ₜ[F] (θ : E)] := by
    rw [hb]
    exact b'.linearIndependent
  apply LinearIndependent.pair_iff.mp hli' a0 a1
  rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [← h0]
  simp [sc, inclR, Algebra.TensorProduct.tmul_mul_tmul]

theorem thetaBas_of (hS : ThetaSpan σ J ψ v) : ThetaBas σ J ψ v := fun hstd hun => by
  obtain ⟨θ, h3, h4⟩ := theta_exists σ v hstd.1
  exact ⟨θ, hS hstd hun θ h4, theta_indep σ v hstd.1 θ h3, h3, h4⟩

theorem resAlg_of_span (hS : ThetaSpan σ J ψ v) (hE : EtaLink σ J ψ v) : ResAlg σ J ψ v :=
  resAlg_of_theta σ J ψ v (thetaBas_of σ J ψ v hS) hE

end PI.OmLocU.Red
end
end
