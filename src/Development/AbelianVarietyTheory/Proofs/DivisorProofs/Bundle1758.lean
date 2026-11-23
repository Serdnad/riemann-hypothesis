module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724

@[expose] public section

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox
open Classical

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem boxCoord_boxVec (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r) (_hd : ∀ τ a, d τ a = 1 ∨ d τ a = -1) :
    ∀ j k, boxCoord z j (boxVec d z k) = if j = k then 1 else 0 := by
  rintro ⟨τ', ⟨⟨a', b'⟩, hj⟩⟩ ⟨τ, ⟨⟨a, b⟩, hk⟩⟩
  have hjk : ((τ', (⟨(a', b'), hj⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)})) =
      (τ, (⟨(a, b), hk⟩ : {ab : Fin r × Fin r // ab ≠ (z, z)}))) ↔ τ' = τ ∧ a' = a ∧ b' = b := by
    constructor
    · intro h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  simp only [hjk]
  simp only [boxCoord, boxVec, LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe]
  simp only [entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply]
  by_cases hτ : τ' = τ
  swap
  · split_ifs <;> simp_all
  subst hτ
  simp only [true_and, if_true]
  clear hjk
  split_ifs with h1 h1' h3 h3 h3 h3 h3 h3
  all_goals simp only [LinearMap.coe_comp, Function.comp_apply, Complex.reLm_coe, Complex.imLm_coe, entryL, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, EuclideanSpace.proj, PiLp.toLp_apply, PiLp.proj_apply, boxEnt, if_true]
  all_goals rcases lt_trichotomy a b with h2 | rfl | h2
  all_goals (try simp only [lt_irrefl, if_false])
  all_goals (try simp only [h2, not_lt_of_gt h2, if_true, if_false])
  all_goals clear _hd
  all_goals (split_ifs with e1 e2 <;> (try obtain ⟨rfl, rfl⟩ := h1') <;> (try obtain ⟨rfl, rfl⟩ := e1) <;> (try obtain ⟨rfl, rfl⟩ := e2) <;> (try simp))
  all_goals (try (simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff, Prod.ext_iff, ne_eq, Prod.mk.injEq] at *; omega))
  all_goals exact absurd ⟨rfl, rfl⟩ h3

end GlobalTheory.CovTop.VolUp.FrameBox
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem sum_boxEnt_diag {r : ℕ} (d : Fin r → ℝ) (z a b : Fin r) (h : (a, b) ≠ (z, z)) :
    ∑ c, boxEnt d z a b c c = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg h1, if_neg h2]
  · subst hab
    have haz : a ≠ z := fun hz => h (by rw [hz])
    have : ∀ c, boxEnt d z a a c c = (if c = a then Complex.I else 0) + (if c = z then -Complex.I else 0) := by
      intro c
      simp only [boxEnt, lt_irrefl, if_false, and_self]
      by_cases h1 : c = a
      · subst h1
        simp [haz]
      · simp [h1]
    simp [this, Finset.sum_add_distrib]
  · refine Finset.sum_eq_zero fun c _ => ?_
    have h1 : ¬ (c = a ∧ c = b) := fun hc => hab.ne' (hc.1.symm.trans hc.2)
    have h2 : ¬ (c = b ∧ c = a) := fun hc => hab.ne' (hc.2.symm.trans hc.1)
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt, if_neg h1, if_neg h2]

theorem boxEnt_skew {r : ℕ} (d : Fin r → ℝ) (hd : ∀ a, d a = 1 ∨ d a = -1) (z a b a' b' : Fin r) :
    boxEnt d z a b b' a' * (d b' : ℂ) + (d a' : ℂ) * (starRingEnd ℂ) (boxEnt d z a b a' b') = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp
  · subst hab
    simp only [boxEnt, lt_irrefl, if_false]
    by_cases h1 : a' = a ∧ b' = a
    · obtain ⟨rfl, rfl⟩ := h1
      simp [mul_comm]
    · have h1' : ¬ (b' = a ∧ a' = a) := fun hc => h1 hc.symm
      simp only [if_neg h1, if_neg h1']
      by_cases h2 : a' = z ∧ b' = z
      · obtain ⟨rfl, rfl⟩ := h2
        simp [mul_comm]
      · have h2' : ¬ (b' = z ∧ a' = z) := fun hc => h2 hc.symm
        simp only [if_neg h2, if_neg h2']
        simp
  · have hne := hab.ne
    have hne' := hab.ne'
    simp only [boxEnt, if_pos hab, if_neg hab.not_gt]
    by_cases h1 : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h1
      rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
    · by_cases h2 : a' = b ∧ b' = a
      · obtain ⟨rfl, rfl⟩ := h2
        rcases hd a' with h | h <;> rcases hd b' with h' | h' <;> simp [hne, hne', h, h']
      · have h1' : ¬ (b' = b ∧ a' = a) := fun hc => h1 hc.symm
        have h2' : ¬ (b' = a ∧ a' = b) := fun hc => h2 hc.symm
        simp only [if_neg h1, if_neg h2, if_neg h1', if_neg h2']
        simp

theorem skewCond_boxVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (d : Ψ → Fin r → ℝ) (z : Fin r), (∀ τ a, d τ a = 1 ∨ d τ a = -1) → ∀ k, SkewCond d (boxVec d z k) := by
  intro E _ _ _ r Ψ d z hd k τ
  by_cases hτ : τ = k.1
  · have he : ∀ a b, boxVec d z k (τ, a, b) = boxEnt (d τ) z k.2.1.1 k.2.1.2 a b := by
      intro a b
      simp only [boxVec, if_pos hτ]
      rw [hτ]
    simp only [he]
    exact ⟨sum_boxEnt_diag _ _ _ _ k.2.2, fun a b => boxEnt_skew _ (hd τ) _ _ _ _ _⟩
  · have he : ∀ a b, boxVec d z k (τ, a, b) = 0 := by
      intro a b
      simp only [boxVec, if_neg hτ]
    simp [he]

end GlobalTheory.CovTop.VolUp.FrameBox
end

section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

private theorem conj_zero_iff' {R : Type} [Ring R] (a b c d S : R) (hba : b * a = 1) (hcd : c * d = 1) :
    S = 0 ↔ a * S * c = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  have e : S = b * (a * S * c) * d := by
    simp only [← mul_assoc, hba, one_mul]; rw [mul_assoc, hcd, mul_one]
  rw [e, h]; simp

private theorem expand' {R : Type} [Ring R] (a b c d y z g : R) (hab : a * b = 1) (hdc : d * c = 1) :
    a * (b * (y * a) * g + g * (c * z * d)) * c = y * (a * g * c) + (a * g * c) * z := by
  have : a * (b * (y * a) * g + g * (c * z * d)) * c = (a * b) * y * (a * g * c) + (a * g * c) * z * (d * c) := by
    simp only [mul_add, add_mul, mul_assoc]
  rw [this, hab, hdc, one_mul, mul_one]

private theorem permJ' {r : ℕ} (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin r) :
    (permM e)ᵀ * Formalism.UG.Jpq p q * permM e = diagonal (fun a => if (e.symm a).isLeft then (1:ℂ) else -1) := by
  ext a b
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply, diagonal_apply, Formalism.UG.Jpq]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; rcases e.symm a with i | i <;> simp
  · rw [if_neg hab]
    have h := e.symm.injective.ne hab
    revert h
    generalize e.symm a = i
    generalize e.symm b = j
    rcases i with i | i <;> rcases j with j | j <;> intro h <;> simp_all [one_apply]

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem mem_comap_realLie_iff_skewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type)
    (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r),
    IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r),
      Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI Y
  rw [Submodule.mem_comap, GlobalTheory.SUVol.DensOne.mem_realLie_iff]
  refine forall_congr' fun τ => ?_
  have hdet := (det_ne_zero_of_isIdent hI τ).1
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  set Gt := G.map τ.1 with hGt
  set Yt : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYt
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hu
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hu
  have hX : Matrix.of (fromFrame x Y τ) = M * Yt * N := rfl
  rw [hX]
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => ((sgnR σ e τ a : ℝ) : ℂ)) with hD
  have hPJP : Pᵀ * J * P = D := by
    rw [hP, hJdef, permJ', hD]
    congr 1; funext a; simp only [sgnR]; split_ifs <;> simp
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hMt : (Mᴴ)ᵀ = M.map (starRingEnd ℂ) := by ext i j; simp
  have hG' : Gt = -(Bᴴ * J * B)ᵀ := by rw [h1, transpose_neg, transpose_transpose, neg_neg]
  have hH : Mᵀ * Gt * M.map (starRingEnd ℂ) = -D := by
    rw [hG', ← hMt, Matrix.mul_neg, Matrix.neg_mul]
    rw [show Mᵀ * (Bᴴ * J * B)ᵀ * (Mᴴ)ᵀ = (Mᴴ * (Bᴴ * J * B) * M)ᵀ by simp only [transpose_mul, Matrix.mul_assoc]]
    have : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
      rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hPJP, hD, diagonal_transpose]
  have hc1 : M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc2 : N.map (starRingEnd ℂ) * M.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht1 : Mᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNM, transpose_one]
  have ht2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMN, transpose_one]
  have htr : (M * Yt * N).trace = ∑ a, Y (τ, a, a) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]; rfl
  rw [htr, and_comm]
  refine and_congr_right fun _ => ?_
  rw [conj_zero_iff' Mᵀ Nᵀ (M.map (starRingEnd ℂ)) (N.map (starRingEnd ℂ)) _ ht2 hc1]
  rw [transpose_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul]
  rw [expand' _ _ _ _ _ _ _ ht1 hc2, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [eq_comm (b := (0 : Matrix (Fin r) (Fin r) ℂ) a b)]
  simp [hD, hYt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact eq_comm

end GlobalTheory.CovTop.VolUp.FrameBox
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne

theorem markOver_zsmul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l l₂ : Level H} {r : ℕ} {L : Lt E r} {mk mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E)} (h : MarkOver l l₂ L mk mk₂) (m : ℤ) :
    MarkOver l l₂ L (m • mk) (m • mk₂) := fun a ha => by
  obtain ⟨u, hu, e⟩ := h a ha
  refine ⟨m • u, zsmul_mem hu _, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.smul_apply, e, smul_add, smul_comm m l.M]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {i : Fin D.R.m}


omit [Algebra T.Q.c.F D.what₂.LL] in
theorem div_mul_phiC {s : T.Q.c.F →+* ℂ} {W : HSp D} {j : ℕ} (hV : T.V j s = W) (hc : CUnit (T.cE j s))
    (cst : (T.U j s).Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (h : GA D W) :
    cst (castDict hV (T.dict j s) h).1 / T.cE j s (castDict hV (T.dict j s) h).1 * phiC T hV a f h =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (castDict hV (T.dict j s) h).1 * castDict hV (T.mu j s) h *
        rdU (T.U j s) f (castDict hV (T.dict j s) h).1 (castDict hV (T.dict j s) h).2) := by
  subst hV
  have h0 : T.cE j s (T.dict j s h).1 ≠ 0 := norm_ne_zero_iff.1 ((hc _).trans_ne one_ne_zero)
  change cst (T.dict j s h).1 / T.cE j s (T.dict j s h).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
    (T.cE j s (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)) =
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * (cst (T.dict j s h).1 * T.mu j s h * rdU (T.U j s) f (T.dict j s h).1 (T.dict j s h).2)
  field_simp

theorem inj_of_indep {K X M : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module ℂ M] {s : K →+* ℂ}
    (c : X →ₛₗ[s] M) (h : ∀ (m : ℕ) (b : Fin m → X), LinearIndependent K b → LinearIndependent ℂ fun j => c (b j)) :
    Function.Injective c := (injective_iff_map_eq_zero c).2 fun x hx => by
  by_contra h0
  exact (h 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem exists_ext (O : OM T R i) (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (hP : Pinned κ v₀ O)
    (σ : D.what₂.LL →+* ℂ) : ∃ σ' : O.c'.F →+* ℂ, σ'.comp O.jL = σ := by
  have hs : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ : (y : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hF ▸ y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hP.lift.field x).trans hx)⟩
  let e := RingEquiv.ofBijective O.jL ⟨O.jL.injective, hs⟩
  exact ⟨σ.comp e.symm.toRingHom, RingHom.ext fun x => congrArg σ (e.symm_apply_apply x)⟩

end GlobalTheory.GalOne

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.riemannianHaar_le_one_of_dim_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  first | exact @GlobalTheory.SUVol.Degenerate.riemHaar_le_one | exact GlobalTheory.SUVol.Degenerate.riemHaar_le_one | (intros; apply GlobalTheory.SUVol.Degenerate.riemHaar_le_one <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  first | exact @GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | exact GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | (intros; apply GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpUnifAH

theorem exists_unif_isFactorAH_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left), M.IsLB → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg M hM e he
  exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp A g hA hg e he M hM

end GlobalTheory.ExpUnifAH
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_appellHumbertFrame_of_exponential : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  first | exact @GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp | exact GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp | (intros; apply GlobalTheory.ExpFrame.exists_isFactorAH_frame_of_isExp <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct

namespace GlobalTheory.PolyRightDeriv

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem hasDerivAt_eval {σ : Type} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (c : ℝ → σ → ℂ)
    (h : ∀ p, HasDerivAt (fun t => c t p) (MvPolynomial.eval (c 0) (δ (MvPolynomial.X p))) 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) P) (MvPolynomial.eval (c 0) (δ P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P p hP =>
    have := hP.mul (h p)
    simp only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
    exact this.congr_deriv (by ring)

theorem hasDerivAt_entry {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A * NormedSpace.exp (t • X)) i j) ((A * X) i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun B => (A * B) i j
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by simp }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  classical
  funext g
  let c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
    fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))
  have hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g *
      NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2 := fun t p => by
    simp only [c, realEntries]
    rw [R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]
    rfl
  have h0 : c 0 = realEntries θ V g := funext fun p => by
    rw [hc, zero_smul, NormedSpace.exp_zero, mul_one]; rfl
  have h := hasDerivAt_eval (matDer τ X.1) c (fun p => by
    simp only [hc]
    convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g)
      (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1
    rw [h0, matDer_X]
    obtain ⟨τ', i, j⟩ := p
    by_cases e : τ' = τ
    · subst e
      simp [atPlace, Matrix.mul_apply, realEntries]
    · simp [atPlace, e, Pi.single_eq_of_ne e]) P
  rw [h0] at h
  exact h.deriv

end GlobalTheory.PolyRightDeriv

end
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := by
  first | exact @GlobalTheory.VacLn.vacLine_of_derEx | exact GlobalTheory.VacLn.vacLine_of_derEx | (intros; apply GlobalTheory.VacLn.vacLine_of_derEx <;> assumption)
end

section

open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

theorem _root_.GlobalTheory.T.thetaFunction_smoothVector_realHeisenberg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  first | exact @GlobalTheory.ThetaSmoothF.sm_of_thetaF | exact GlobalTheory.ThetaSmoothF.sm_of_thetaF | (intros; apply GlobalTheory.ThetaSmoothF.sm_of_thetaF <;> assumption)
end
