module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle166
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle214
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle207
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviRat

open GlobalTheory.AdaptedMove GlobalTheory.FlagConj GlobalTheory.PointEquivariance

theorem mem_conj_iff (I : AutInst) (x : I.Gf) (c : I.GA) (γ : GL (Fin I.n) I.E)
    (hc : I.fmat c.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    x⁻¹ * c.2 * x ∈ I.Kset ↔ ratIso I γ (lamX I (1, x)) = lamX I (1, x) := by
  have hk := GlobalTheory.PointEquivariance.lamX_mul_eq_iff I ((1 : I.Ginf), x) (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x))
  have hcx : ((1 : I.Ginf), x) * (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x)) = c * ((1 : I.Ginf), x) := by
    group
  rw [hcx, GlobalTheory.PointEquivariance.lamX_rat I ((1 : I.Ginf), x) c γ hc] at hk
  exact hk

private theorem mem_UJ_iff_flag_measures {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (g : GL (Fin m) E) :
    g ∈ Formalism.UG.UJ (starRingEnd E) J ↔ (g : Matrix (Fin m) (Fin m) E)ᴴ * J * g = J := by
  have key : ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ = (g : Matrix (Fin m) (Fin m) E)ᴴ := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  show ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ * J * g = J ↔ _
  rw [key]

private theorem inv_mul_eq_mul_inv_of_mul_eq_mul {R : Type} [CommRing R] {m p : ℕ} (G G' : Matrix (Fin m) (Fin m) R)
    (C C' : Matrix (Fin p) (Fin p) R) (X : Matrix (Fin m) (Fin p) R) (hG : G' * G = 1) (hC : C * C' = 1)
    (h : G * X = X * C) : G' * X = X * C' := by
  calc G' * X = G' * (X * C) * C' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hC, Matrix.mul_one]
    _ = X * C' := by rw [← h, ← Matrix.mul_assoc, hG, Matrix.one_mul]

private theorem lat_mulVec_lemma_3 (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf)
    (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hlat : ∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l))
    (G : Matrix (Fin I.n) (Fin I.n) I.E) (c A : ∀ i, Matrix (Fin (j i)) (Fin (j i)) I.E)
    (d : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)
    (hc : ∀ i, ∀ u ∈ Λ i, c i *ᵥ u ∈ Λ i) (hA : ∀ i, ∀ u ∈ Λ i, A i *ᵥ u ∈ Λ i)
    (hd : ∀ y ∈ lamX I₀ (1, x₀), d *ᵥ y ∈ lamX I₀ (1, x₀))
    (hT : ∀ i, G * T i = T i * c i) (hT' : ∀ i, G * T' i = T' i * (A i)ᴴ) (h₀ : G * T₀ = T₀ * d.map e) :
    ∀ z ∈ lamX I (1, xf), G *ᵥ z ∈ lamX I (1, xf) := by
  intro z hz
  obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := (hlat z).1 hz
  refine (hlat _).2 ⟨fun i => c i *ᵥ u i, fun i => (A i)ᴴ *ᵥ u' i, d *ᵥ y, fun i => hc i _ (hu i), ?_, hd y hy, ?_⟩
  · intro i t ht
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact hu' i _ (hA i t ht)
  · beta_reduce
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT i, ← Matrix.mulVec_mulVec]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT' i, ← Matrix.mulVec_mulVec]
    · rw [Matrix.mulVec_mulVec, h₀, ← Matrix.mulVec_mulVec]
      congr 1
      funext l
      exact (RingHom.map_mulVec (e : I₀.E →+* I.E) d y l).symm

theorem exists_rat_block : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hAd γ hγ g₀ hg₀
  obtain ⟨he, hn, -, h1, h2, h3, hlat, -⟩ := hAd
  obtain ⟨c₀, ⟨δ, hδU, hδP, hδf⟩, rfl, hc₀K⟩ := hg₀
  have hδL := (mem_conj_iff I₀ x₀ c₀ δ hδf).1 hc₀K
  have hJ : I.Jᴴ = I.J := by
    have hH : (I.J.map (starRingEnd I.E))ᵀ = I.J := I.J_herm
    ext r s
    have := congrArg (fun M => M r s) hH
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this
    rw [Matrix.conjTranspose_apply, ← this]
    rfl
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    intro h
    apply I₀.J_det
    have h' : (e : I₀.E →+* I.E) I₀.J.det = 0 := by
      rw [RingHom.map_det]
      exact h
    simpa using h'
  have hsemi : Function.Semiconj e star star := he
  have hδU' := (mem_UJ_iff_flag_measures I₀.J δ).1 hδU
  obtain ⟨U, hU⟩ : ∃ U : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) := ⟨_, fun _ => rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E,
      U₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := ⟨_, rfl⟩
  have g1 : ∀ i k, (U i)ᴴ * I.J * U k = 0 ∧ (U' i)ᴴ * I.J * U' k = 0 ∧
      (i ≠ k → (U i)ᴴ * I.J * U' k = 0) := by
    intro i k
    obtain ⟨a1, a2, a3⟩ := h1 i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [hU, hU, GlobalTheory.AdaptedMove.gram_mul, a1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU', GlobalTheory.AdaptedMove.gram_mul, a2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, a3 hik, Matrix.mul_zero, Matrix.zero_mul]
  have g2 : ∀ i, (U i)ᴴ * I.J * U' i = 1 ∧ (U i)ᴴ * I.J * U₀ = 0 ∧ (U' i)ᴴ * I.J * U₀ = 0 := by
    intro i
    obtain ⟨b1, b2, b3⟩ := h2 i
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, b1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.inv_mul,
        Matrix.conjTranspose_one]
    · rw [hU, hU₀, GlobalTheory.AdaptedMove.gram_mul, b2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU₀, GlobalTheory.AdaptedMove.gram_mul, b3, Matrix.mul_zero, Matrix.zero_mul]
  have g3 : U₀ᴴ * I.J * U₀ = I₀.J.map e := by
    rw [hU₀, GlobalTheory.AdaptedMove.gram_mul, h3, ← Matrix.conjTranspose_map _ hsemi]
    calc ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ).map e * I₀.J.map e * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e
        = ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ * I₀.J * δ).map (e : I₀.E →+* I.E) := by
          rw [Matrix.map_mul, Matrix.map_mul]
          rfl
      _ = I₀.J.map e := by
          rw [hδU']
          rfl
  obtain ⟨Γ, hΓJ, hΓT, hΓT', hΓ₀⟩ :=
    GlobalTheory.FlagConj.exists_unitary_adapted hn I.J hJ (I₀.J.map e) hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hΓU : Γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := (mem_UJ_iff_flag_measures I.J Γ).2 hΓJ
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.FlagConj.exists_point I Γ hΓU
  have hγf : ∀ i, ∀ u ∈ Λ i, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i :=
    fun i u hu => (hγ i u).2 hu
  have hγb : ∀ i, ∀ u ∈ Λ i, (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i := by
    intro i u hu
    apply (hγ i _).1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hu
  have hδf' : ∀ y ∈ lamX I₀ (1, x₀), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso]
    exact ⟨y, hy, rfl⟩
  have hδb : ∀ y ∈ lamX I₀ (1, x₀),
      ((δ⁻¹ : GL (Fin I₀.n) I₀.E) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy'
  have hT : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => (hΓT i).trans (hU i)
  have hT' : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    fun i => (hΓT' i).trans (hU' i)
  have hT₀ : (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e :=
    hΓ₀.trans hU₀
  have hΓi : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * Γ = 1 := Units.inv_mul Γ
  have hTb : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T i =
      T i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi (Units.mul_inv (γ i)) (hT i)
  have hT'b : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ := by
    intro i
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ (hT' i)
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hT₀b : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ =
      T₀ * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := by
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ hT₀
    have hm : (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e *
        (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e =
        ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *
          (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)).map (e : I₀.E →+* I.E) :=
      (Matrix.map_mul).symm
    rw [hm, Units.mul_inv]
    exact Matrix.map_one _ (map_zero e) (map_one e)
  have hfw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat Γ
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) δ hγf hγb hδf' hT hT' hT₀
  have hbw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E)
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) hγb hγf hδb hTb hT'b hT₀b
  have hLat : ratIso I Γ (lamX I (1, xf)) = lamX I (1, xf) := by
    ext z
    rw [GlobalTheory.FlagConj.mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfw y hy
    · intro hz
      refine ⟨(((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, hbw z hz, ?_⟩
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨c.1, ⟨c, ⟨Γ, hΓU, hc1, hc2⟩, rfl, (mem_conj_iff I xf c Γ hc2).2 hLat⟩,
    (Γ : Matrix (Fin I.n) (Fin I.n) I.E), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), hc1, hδP, hT, hT₀⟩

end GlobalTheory.LeviRat
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem star_dot_Jm {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (qEps ε x : ℂ) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (x i)
  split_ifs
  · simp [hi]
  · simp [hi]

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  unfold Formalism.REAL.UJ Formalism.UG.UJ Formalism.REAL.inUJ
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε ↔
    (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [hc]

theorem exists_closedEmbedding_unitary_orthogonal (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool)
    (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (hn : m + 1 = n) (hq : qEps ε x₀ = sgn ℝ s)
    (hx : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧
      ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  unfold uMat
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hdet : (Formalism.REAL.Jm ε').det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by by_cases h : ε' a <;> simp [h]
  have hβ : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [star_dot_Jm, hq]
    cases s <;> simp [sgn]
  obtain ⟨u, A', hA'B, hA'x, huB, hux, hres, hBJx⟩ :=
    exists_dual_of_anisotropic_orthogonal ℂ n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ B hn hJh hdet hβ hx hB
  have hcT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ), Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro p q M
    ext i k
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  have hstar : (fun i => starRingEnd ℂ (x₀ i)) = star x₀ := by
    funext i
    simp [Complex.star_def]
  obtain ⟨j, hjmat, hjrange⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer ℂ (starRingEnd ℂ) n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ u B A'
    (by rw [hstar]; exact isUnit_iff_ne_zero.mpr hβ) (by rw [hstar]; exact hx) (by rw [hcT]; exact hBJx)
    (by rw [hcT]; exact hB) hA'B hA'x huB hux hres
  obtain ⟨jj, hjj, hrange⟩ : ∃ jj : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε,
      (∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        vecMulVec x₀ u + B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A') ∧
      ∀ h : Formalism.REAL.UJ ε, ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ → ∃ g, jj g = h := by
    refine ⟨(MulEquiv.subgroupCongr (realUJ_eq ε)).toMonoidHom.comp
      (j.comp (MulEquiv.subgroupCongr (realUJ_eq ε')).symm.toMonoidHom), fun g => hjmat _, ?_⟩
    intro h hh
    obtain ⟨g', hg'⟩ := hjrange ((MulEquiv.subgroupCongr (realUJ_eq ε)).symm h) hh
    refine ⟨MulEquiv.subgroupCongr (realUJ_eq ε') g', ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hg'
  have h0 : vecMulVec x₀ u * B = 0 := by
    ext i k
    have hk := congrFun huB k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk
    change (∑ j, (x₀ i * u j) * B j k) = 0
    simp only [mul_assoc, ← Finset.mul_sum, hk, mul_zero]
  have hv : vecMulVec x₀ u *ᵥ x₀ = x₀ := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ k, u k * x₀ k = 1 from hux, mul_one]
  have hfix : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ := by
    intro g
    rw [hjj, add_mulVec, hv, ← mulVec_mulVec, hA'x, mulVec_zero, add_zero]
  have hcomm : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B =
      B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    intro g
    rw [hjj, Matrix.add_mul, h0, zero_add, Matrix.mul_assoc (B * _), hA'B, Matrix.mul_one]
  have hback : ∀ M : Matrix (Fin m) (Fin m) ℂ, A' * (vecMulVec x₀ u + B * M * A') * B = M := by
    intro M
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A' (vecMulVec x₀ u), h0, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hA'B, Matrix.mul_one, ← Matrix.mul_assoc, hA'B, Matrix.one_mul]
  have hval' : Continuous fun g : Formalism.REAL.UJ ε' => ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv' : Continuous fun g : Formalism.REAL.UJ ε' => (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hjinv : ∀ g, ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      vecMulVec x₀ u + B * (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A' := by
    intro g
    have h1 := hjj g⁻¹
    rw [map_inv] at h1
    exact h1
  have hcont : Continuous jj := by
    refine continuous_induced_rng.2 ?_
    rw [Units.continuous_iff]
    constructor
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hval').matrix_mul continuous_const))
        fun g => (hjj g).symm
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hinv').matrix_mul continuous_const))
        fun g => (hjinv g).symm
  let ψ : Formalism.REAL.UJ ε → Matrix (Fin m) (Fin m) ℂ × (Matrix (Fin m) (Fin m) ℂ)ᵐᵒᵖ := fun h =>
    (A' * ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B,
      MulOpposite.op (A' * (((h : GL (Fin n) ℂ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B))
  have hψc : Continuous ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    · exact MulOpposite.continuous_op.comp ((continuous_const.matrix_mul
        (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul continuous_const)
  have hψ : ∀ g, ψ (jj g) = Units.embedProduct _ (g : GL (Fin m) ℂ) := by
    intro g
    refine Prod.ext ?_ ?_
    · show A' * ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B = ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjj, hback]
    · show MulOpposite.op (A' * ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B) =
        MulOpposite.op ((((g : GL (Fin m) ℂ))⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjinv, hback]
  have hind : Topology.IsInducing jj := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    have he : ψ ∘ jj = fun g : Formalism.REAL.UJ ε' => Units.embedProduct _ (g : GL (Fin m) ℂ) := funext hψ
    rw [he]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective jj := by
    intro a b hab
    have hc := congrArg ψ hab
    rw [hψ, hψ] at hc
    exact Subtype.ext (Units.ext (congrArg Prod.fst hc))
  have hrng : Set.range jj = {h : Formalism.REAL.UJ ε | ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀} := by
    ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g
    · intro hh
      exact hrange h hh
  have hclosed : IsClosed (Set.range jj) := by
    rw [hrng]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const)
      continuous_const
  exact ⟨jj, ⟨⟨hind, hinj⟩, hclosed⟩, fun g => ⟨hfix g, hcomm g⟩⟩

end GlobalTheory.StabUnfold
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
end

section

open Matrix

theorem _root_.GlobalTheory.T.realMatrix_mem_besselUnipotent_of_frame : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  first | exact @GlobalTheory.DegVol.FrameUnip.mem_Nset | exact GlobalTheory.DegVol.FrameUnip.mem_Nset | (intros; apply GlobalTheory.DegVol.FrameUnip.mem_Nset <;> assumption)
end
