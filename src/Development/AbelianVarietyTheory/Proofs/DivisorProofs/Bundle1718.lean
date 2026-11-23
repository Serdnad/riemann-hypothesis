module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

theorem exists_inv_of_not_dvd_discr (E : Type) [Field E] [NumberField E] {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V)) (hd : ¬ (g : ℤ) ∣ discr E) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical
  let bs := RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e' : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ).symm
  let A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) V :=
    fun i k => χ (e' k) (bs i)
  have hAij : ∀ i k, A i k = χ (e' k) (bs i) := fun _ _ => rfl
  let AF : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) F :=
    fun i k => φ (e' k) (bs i : E)
  have hAF : AF.map j = Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => (bs i : E)) e := by
    ext i k
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_symm]
    show j (φ (e' k) (bs i : E)) = (e k) (bs i : E)
    rw [hφ]
    rfl
  have hdF : AF.det ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, hAF,
      ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, map_intCast]
    have hb : (fun i => (bs i : E)) = ⇑(integralBasis E) := funext fun i => (integralBasis_apply E i).symm
    rw [hb, ← coe_discr, map_intCast]
  have hdV : A.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hA : (algebraMap V Fr).mapMatrix A = io.mapMatrix AF := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAij, AF, hχ]
      rfl
    rw [hA, ← RingHom.map_det, ← map_pow, hdF, map_intCast]
  have hu : IsUnit A.det := by
    have h := isUnit_of_not_dvd g hg hgV _ hd
    rw [← hdV] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  refine ⟨fun i τ => A⁻¹ (e'.symm τ) i, ?_, ?_⟩
  · intro σ τ
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul A hu) (e'.symm τ)) (e'.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij, Equiv.apply_symm_apply] at h1
    rw [show (∑ i, χ σ (bs i) * A⁻¹ (e'.symm τ) i) = ∑ i, A⁻¹ (e'.symm τ) i * χ σ (bs i) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : σ = τ
    · subst h; simp
    · rw [if_neg (fun h' => h (e'.symm.injective h').symm), if_neg h]
  · intro i i'
    have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i') i
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij] at h1
    rw [← Equiv.sum_comp e' (fun τ => A⁻¹ (e'.symm τ) i * χ τ (bs i'))]
    simp only [Equiv.symm_apply_apply]
    rw [show (∑ k, A⁻¹ k i * χ (e' k) (bs i')) = ∑ k, χ (e' k) (bs i') * A⁻¹ k i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem red_bijective (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p)
    (hp : UnramIn E p) : Function.Bijective (red io X) := by
  classical
  haveI : IsDomain X.O := X.ints.hom_inj.isDomain _
  obtain ⟨Cm, hAC, hCA⟩ := exists_inv_of_not_dvd_discr E (V := X.O) (Fr := X.C) X.ints.hom_inj
    (c.F.val : c.F →+* ℂ) (X.ιF.comp io) (embF c) (fun σ x => by simp [embF])
    (embO io X) (fun σ a => algebraMap_embO io X σ a) p Fact.out X.nonunit.out hp
  set b := RingOfIntegers.basis E
  let Cr : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → ResidueField X.O := fun i τ => residue X.O (Cm i τ)
  have hAC' : ∀ σ τ, ∑ i, red io X σ (b i) * Cr i τ = if σ = τ then 1 else 0 := by
    intro σ τ
    have := congrArg (residue X.O) (hAC σ τ)

    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  have hCA' : ∀ i i', ∑ τ, Cr i τ * red io X τ (b i') = if i = i' then 1 else 0 := by
    intro i i'
    have := congrArg (residue X.O) (hCA i i')

    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  refine ⟨fun σ τ hst => ?_, fun χ => ?_⟩
  · by_contra hne
    have h1 := hAC' σ τ
    rw [if_neg hne, hst, hAC' τ τ, if_pos rfl] at h1
    exact one_ne_zero h1
  · let ρ : 𝓞 E →+* Module.End (ResidueField X.O) (ResidueField X.O) :=
      (Algebra.lmul (ResidueField X.O) (ResidueField X.O)).toRingHom.comp χ
    obtain ⟨mσ, hm, hs⟩ := ((decomp_of_inv ρ (red io X) b Cr hAC' hCA').1 1)
    obtain ⟨σ, hσ⟩ : ∃ σ, mσ σ ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    refine ⟨σ, RingHom.ext fun a => ?_⟩
    have : χ a * mσ σ = red io X σ a * mσ σ := hm σ a
    exact (mul_right_cancel₀ hσ this).symm

end GlobalTheory.PrimePart
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.FrameBox

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def sgnR {κ : Type} {p q : κ → ℕ} {Ψ : Finset (E →+* ℂ)} (σ : κ ≃ Ψ)
    (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (τ : Ψ) (a : Fin r) : ℝ :=
  if ((e (σ.symm τ)).symm a).isLeft then 1 else -1

def SkewCond {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) : Prop :=
  ∀ τ : Ψ, (∑ a, Y (τ, a, a) = 0) ∧
    ∀ a b, Y (τ, b, a) * (d τ b : ℂ) + (d τ a : ℂ) * (starRingEnd ℂ) (Y (τ, a, b)) = 0

def boxEnt (d : Fin r → ℝ) (z a b a' b' : Fin r) : ℂ :=
  if a < b then (if a' = a ∧ b' = b then 1 else if a' = b ∧ b' = a then -((d a * d b : ℝ) : ℂ) else 0)
  else if b < a then
    (if a' = b ∧ b' = a then Complex.I else if a' = a ∧ b' = b then Complex.I * ((d a * d b : ℝ) : ℂ) else 0)
  else (if a' = a ∧ b' = a then Complex.I else if a' = z ∧ b' = z then -Complex.I else 0)


open Classical in
def boxVec {Ψ : Finset (E →+* ℂ)} (d : Ψ → Fin r → ℝ) (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
  WithLp.toLp 2 fun m => if m.1 = k.1 then boxEnt (d k.1) z k.2.1.1 k.2.1.2 m.2.1 m.2.2 else 0

def entryL {Ψ : Finset (E →+* ℂ)} (m : Ψ × Fin r × Fin r) : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℂ :=
  ((EuclideanSpace.proj m : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →L[ℂ] ℂ) : _ →ₗ[ℂ] ℂ).restrictScalars ℝ

def boxCoord {Ψ : Finset (E →+* ℂ)} (z : Fin r) (k : Ψ × {ab : Fin r × Fin r // ab ≠ (z, z)}) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] ℝ :=
  if k.2.1.1 < k.2.1.2 then Complex.reLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.2)
  else if k.2.1.2 < k.2.1.1 then Complex.imLm ∘ₗ entryL (k.1, k.2.1.2, k.2.1.1)
  else Complex.imLm ∘ₗ entryL (k.1, k.2.1.1, k.2.1.1)

end GlobalTheory.CovTop.VolUp.FrameBox

namespace GlobalTheory.CovTop.VolUp.FrameBox
open Matrix

theorem det_ne_zero_of_isIdent {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ (G.map τ.1).det ≠ 0 := by
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  have hPA : (Pᵀ * B) * M = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hdetM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPA
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  refine ⟨hdetM, fun h => ?_⟩
  have hJ : J * J = 1 := by simp [hJdef, Formalism.UG.Jpq, fromBlocks_multiply]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hX : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
    rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hsq : (Pᵀ * J * P) * (Pᵀ * J * P) = 1 := by
    have e1 : (Pᵀ * J * P) * (Pᵀ * J * P) = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [Matrix.mul_assoc]
    rw [e1, permM_mul_transpose, Matrix.mul_one, Matrix.mul_assoc Pᵀ J J, hJ, Matrix.mul_one, transpose_mul_permM]
  have hd0 : (Bᴴ * J * B).det = 0 := by
    rw [h1, det_neg, det_transpose, h, mul_zero]
  have := congrArg Matrix.det hsq
  rw [← hX, det_mul, det_mul, det_mul, hd0] at this
  simp at this

end GlobalTheory.CovTop.VolUp.FrameBox
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.BallCover

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_lower (n : Type) [Fintype n] [DecidableEq n] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < ρ → ‖Y‖ ≤ 2 * ‖NormedSpace.exp Y - 1‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero] at this
  have h1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 2 * ‖Y‖ := this
  have h2 : ‖Y‖ ≤ ‖NormedSpace.exp Y - 1‖ + ‖NormedSpace.exp Y - 1 - Y‖ := by
    calc ‖Y‖ = ‖(NormedSpace.exp Y - 1) - (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

end Exp

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frBall_subset_chartExp_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  intro E _ _ _ r Ψ G x hG hx δ hδ
  obtain ⟨ρ, hρ, hexp⟩ := exists_exp_lower (Fin r)
  let cj : (Ψ → Fin r → Fin r → ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun X τ => (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ
  have hcj : Continuous cj :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  let U : Set (realLie Ψ G) := {X | ‖X‖ < δ ∧ ∀ τ, ‖cj X.1 τ‖ < ρ}
  have hU : U ∈ nhds 0 := by
    refine IsOpen.mem_nhds ?_ ?_
    · change IsOpen ({X : realLie Ψ G | ‖X‖ < δ} ∩
        {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ})
      refine (isOpen_lt continuous_norm continuous_const).inter ?_
      change IsOpen {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ}
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun τ =>
        isOpen_lt ((continuous_apply τ).comp (hcj.comp continuous_subtype_val)).norm continuous_const
    · refine ⟨by simpa using hδ, fun τ => ?_⟩
      have e : cj (0 : realLie Ψ G).1 τ = 0 := by
        change (mat x τ)⁻¹ * (0 : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 0
        simp
      rw [e, norm_zero]; exact hρ
  have hev := GlobalTheory.SUVol.DensOne.eventually_mem_image Ψ G hG hU
  rw [Filter.eventually_comap] at hev
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.1 hev
  let bk : (Ψ → Matrix (Fin r) (Fin r) ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun A τ => mat x τ * A τ * (mat x τ)⁻¹
  have hbk : Continuous bk :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  have hbk0 : bk 0 = 0 := by funext τ; simp [bk]
  obtain ⟨ε₁, hε₁, hbkε⟩ := Metric.continuous_iff.1 hbk 0 η hη
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ g hg => ?_⟩
  let A : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1
  have hA : ‖A‖ < ε := (pi_norm_lt_iff hε).2 fun τ => (Matrix.norm_lt_iff hε).2 fun a b => hg τ a b
  have hbkA : bk A = GlobalTheory.SUVol.DensOne.matR Ψ G g - 1 := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1) * (mat x τ)⁻¹ =
      GlobalTheory.SUVol.DensOne.matR Ψ G g τ - 1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hx τ).isUnit,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hdist : dist (GlobalTheory.SUVol.DensOne.matR Ψ G g) 1 < η := by
    have := hbkε A (by rw [dist_zero_right]; linarith)
    rw [hbk0, dist_zero_right, hbkA] at this
    rwa [dist_eq_norm]
  obtain ⟨X, ⟨hXδ, hXρ⟩, rfl⟩ := hh hdist g rfl
  refine ⟨X, ⟨hXδ, fun τ a b => ?_⟩, rfl⟩
  have hY := hexp (cj X.1 τ) (hXρ τ)
  have he : NormedSpace.exp (cj X.1 τ) - 1 = A τ := by
    change NormedSpace.exp ((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) - 1 =
      (mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1
    rw [Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
  have hAτ : ‖A τ‖ < ε := lt_of_le_of_lt (norm_le_pi_norm A τ) hA
  rw [he] at hY
  calc ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ = ‖cj X.1 τ a b‖ := rfl
    _ ≤ ‖cj X.1 τ‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖A τ‖ := hY
    _ < 2 * ε := by linarith

end Main

end GlobalTheory.CovTop.VolUp.BallCover
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_apply' (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x : G) (v : V) (y : G) :
    secM ι ρ K x v y =
      ((stabCard ι K x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) v := rfl

theorem finsum_apply_eq (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) {φ : G → V}
    (hφ : φ ∈ eqvM ι ρ K) (x y : G) (hs : Set.Finite {h : H | (ι h * x)⁻¹ * y ∈ K}) :
    (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K then ρ h else 0) (φ x) =
      Nat.card {h : H | (ι h * x)⁻¹ * y ∈ K} • φ y := by
  rw [finsum_eq_sum_of_support_subset _ (s := hs.toFinset) ?_]
  · rw [LinearMap.sum_apply,
      Finset.sum_congr rfl (g := fun _ => φ y) ?_, Finset.sum_const, ← Nat.card_eq_card_finite_toFinset]
    intro h hh
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
    rw [if_pos hh, ← hφ.1 h x, ← hφ.2 _ hh (ι h * x), mul_inv_cancel_left]
  · intro h hh
    rw [Function.mem_support] at hh
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    by_contra hc
    exact hh (if_neg hc)

theorem card_eq (ι : H →* G) (hι : Function.Injective ι) (K : Subgroup G) (x : G) (h₀ : H) {k₀ : G}
    (hk₀ : k₀ ∈ K) :
    ∃ e : {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} → ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom),
      Function.Bijective e := by
  have key : ∀ h : H, (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K ↔ x⁻¹ * ι (h⁻¹ * h₀) * x ∈ K := by
    intro h
    have : (ι h * x)⁻¹ * (ι h₀ * x * k₀) = x⁻¹ * ι (h⁻¹ * h₀) * x * k₀ := by
      simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]
    rw [this, Subgroup.mul_mem_cancel_right K hk₀]
  refine ⟨fun h => ⟨ι (h.1⁻¹ * h₀), Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
    Subgroup.mem_map.mpr ⟨x⁻¹ * ι (h.1⁻¹ * h₀) * x, (key h.1).mp h.2, ?_⟩⟩⟩, ?_, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · intro a b hab
    have := hι (congrArg Subtype.val hab)
    exact Subtype.ext (by simpa using this)
  · rintro ⟨g, hg⟩
    obtain ⟨⟨s, rfl⟩, hm⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hm
    refine ⟨⟨h₀ * s⁻¹, ?_⟩, ?_⟩
    · show (ι (h₀ * s⁻¹) * x)⁻¹ * (ι h₀ * x * k₀) ∈ K
      rw [key]
      have : x⁻¹ * ι ((h₀ * s⁻¹)⁻¹ * h₀) * x = k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hks
        simp [← hks, mul_assoc]
      rw [this]; exact hk
    · apply Subtype.ext
      simp

end GlobalTheory.BCT.TraceBlocks.Decomp

namespace GlobalTheory.BCT.TraceBlocks.Decomp

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

theorem secM_self (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K : Subgroup G)
    {φ : G → V} (hφ : φ ∈ eqvM ι ρ K) (x : G) [Finite ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom)]
    (h₀ : H) {k₀ : G} (hk₀ : k₀ ∈ K) :
    secM ι ρ K x (φ x) (ι h₀ * x * k₀) = φ (ι h₀ * x * k₀) := by
  obtain ⟨e, he⟩ := card_eq ι hι K x h₀ hk₀
  have hfin : Set.Finite {h : H | (ι h * x)⁻¹ * (ι h₀ * x * k₀) ∈ K} :=
    Set.finite_coe_iff.mp (Finite.of_injective e he.1)
  rw [secM_apply', finsum_apply_eq ι ρ K hφ x _ hfin, Nat.card_congr (Equiv.ofBijective e he),
    ← Nat.cast_smul_eq_nsmul ℂ]
  have hpos : (0 : ℕ) < Nat.card ↥(ι.range ⊓ K.map (MulAut.conj x).toMonoidHom) := Nat.card_pos
  exact inv_smul_smul₀ (Nat.cast_ne_zero.mpr hpos.ne') _

theorem secM_off (ι : H →* G) (ρ : Representation ℂ H V) (K : Subgroup G) (x y : G) (v : V)
    (hy : ∀ h : H, (ι h * x)⁻¹ * y ∉ K) : secM ι ρ K x v y = 0 := by
  rw [secM_apply']
  simp only [hy, if_false, finsum_zero, LinearMap.zero_apply, smul_zero]

end GlobalTheory.BCT.TraceBlocks.Decomp


open GlobalTheory.BCT.TraceBlocks.Decomp in
theorem GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K' : Subgroup G), Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) → (∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) → ∀ φ ∈ eqvM ι ρ K', ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G), secM ι ρ K' (Quotient.out q) (φ (Quotient.out q)) = φ := by
  intro G H V _ _ _ _ ι hι ρ K' hQ hS φ hφ
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G))
  funext y
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply, Finset.sum_eq_single (DoubleCoset.mk ι.range K' y)]
  · obtain ⟨g, hg, k₀, hk₀, hy⟩ := (@DoubleCoset.eq _ _ ι.range K'
      (Quotient.out (DoubleCoset.mk ι.range K' y)) y).mp (DoubleCoset.out_eq' _)
    obtain ⟨h₀, rfl⟩ := hg
    haveI := hS (Quotient.out (DoubleCoset.mk ι.range K' y))
    have key := secM_self ι hι ρ K' hφ (Quotient.out (DoubleCoset.mk ι.range K' y)) h₀ hk₀
    rw [← hy] at key
    exact key
  · intro q _ hq
    refine secM_off ι ρ K' _ y _ fun h hh => hq ?_
    refine (DoubleCoset.out_eq' q).symm.trans ((@DoubleCoset.eq _ _ _ _ _ _).mpr
      ⟨ι h, ⟨h, rfl⟩, _, hh, (mul_inv_cancel_left _ _).symm⟩)
  · intro h
    exact absurd (Finset.mem_univ _) h
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.weilRep_derivative_law_of_L2Isometric : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ {G : Type} [Group G] (om : G →* Module.End ℂ ((κ → AdeleRing (𝓞 F) F) → ℂ)),
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, om p φ ∈ GlobalTheory.WeilM.schA F κ) →
      ∀ (M : G → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) →
      ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p φ) = GlobalTheory.WeilL2Words.l2A F μ φ) →
      ∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, GlobalTheory.WeilL2Words.dS F ψ h (om p φ) = om p (GlobalTheory.WeilL2Words.dS F ψ (M p h) φ) := by
  first | exact @GlobalTheory.WeilL2Words.dS_om_eq | exact GlobalTheory.WeilL2Words.dS_om_eq | (intros; apply GlobalTheory.WeilL2Words.dS_om_eq <;> assumption)
end
