module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FlagSpanVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle059
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentSums
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeEqualityFromTestFunctions
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem zhat_norm_bound : C2.ZhatBound := by
  apply PI.PolynomialProperness.GN.zhat_norm_linear_bound <;> assumption

end Formalism.FourierDecayAlt.P
end

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxDs2

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def NNMaj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ),
    TransportedAlt k r A m →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * B.gN (B.sgs p g) ^ (-A) ≤ b p

def JDomBound : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ Om k r D.z D.z' →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
          u.length + v.length ≤ m → ∀ g ∈ K, ∀ᵐ p ∂D.μSS,
            ‖B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g‖ ≤ b p

def JDomMeas : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    TransportedAlt k r A m → B.InCC A m F →
    ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m →
      ∀ g ∈ Om k r D.z D.z',
        AEStronglyMeasurable (fun p => B.rho D p (B.dLR (u.map (AdL p)) (v.map (AdR p)) F) g) D.μSS

theorem jDom_of_parts : JDomMeas → JDomBound → Formalism.FourierDecayAlt.JF.JDom := fun hM hB k r Wp Wq _ _ _ _ _ _ D A m F hT hC =>
  ⟨hM k r Wp Wq D A m F hT hC, hB k r Wp Wq D A m F hT hC⟩

variable {k r : ℕ}

private theorem gv_mul_lemma (a b : Mat k r) (ha : a ∈ GV k r) (hb : b ∈ GV k r) : a * b ∈ GV k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma sL_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sL p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨⟨h11, -⟩, ⟨h12, -⟩, -, -⟩ := hp
  unfold sL
  exact gv_mul_lemma _ _ h12 h11

lemma sR_mem {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {D : RealPlaceData k r Wp Wq} {p : SS k r} (hp : D.inSS p) : sR p ∈ GV k r := by
  unfold RealPlaceData.inSS at hp
  unfold UWset QuantumDeterminants.Nset at hp
  obtain ⟨-, -, ⟨h21, -⟩, ⟨h22, -⟩⟩ := hp
  unfold sR
  exact gv_mul_lemma _ _ h22 h21

lemma pn_lr (p : SS k r) (u v : List (Mat k r)) :
    B4.pn (B4.lr (u.map (AdL p)) (v.map (AdR p))) =
      (u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod := by
  simp [B4.pn, B4.lr, List.map_append, List.prod_append, List.map_map, Function.comp_def]

private theorem inLie_inv_mul_mul_of_mem_gv {y X : Mat k r} (hy : y ∈ GV k r) (hX : inLie k r X) : inLie k r (y⁻¹ * X * y) := by
  have hHH : Hpk k r * Hpk k r = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  have hHH' : ∀ A : Mat k r, Hpk k r * (Hpk k r * A) = A := fun A => by rw [← mul_assoc, hHH, one_mul]
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  have hinv : y⁻¹ = Hpk k r * yᴴ * Hpk k r := by
    apply Matrix.inv_eq_left_inv
    simp only [mul_assoc] at hy' ⊢
    rw [hy', hHH]
  have e1 : (y⁻¹ * X * y)ᴴ * Hpk k r = yᴴ * (Xᴴ * Hpk k r) * y := by
    rw [hinv]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Formalism.QuantumDeterminants.GBasic.Hpk_herm, mul_assoc,
      hHH, mul_one]
  have e2 : Hpk k r * (y⁻¹ * X * y) = yᴴ * (Hpk k r * X) * y := by
    rw [hinv]
    simp only [mul_assoc, hHH']
  show (y⁻¹ * X * y)ᴴ * Hpk k r + Hpk k r * (y⁻¹ * X * y) = 0
  rw [e1, e2, ← add_mul, ← mul_add, hX', mul_zero, zero_mul]

lemma allLie_ad {p : SS k r} (hL : sL p ∈ GV k r) (hR : sR p ∈ GV k r) {u v : List (Mat k r)}
    (hu : ∀ X ∈ u, unitLie k r X) (hv : ∀ X ∈ v, unitLie k r X) :
    B4.AllLie (B4.lr (u.map (AdL p)) (v.map (AdR p))) := by
  unfold B4.AllLie B4.lr AdL AdR
  intro x hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨_, ⟨X, hX, rfl⟩, rfl⟩ | ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  · exact inLie_inv_mul_mul_of_mem_gv hL (hu X hX).1
  · exact inLie_inv_mul_mul_of_mem_gv hR (hv X hX).1

theorem jDomBound_of_nnMaj : NNMaj → JDomBound := by
  intro hNN k r Wp Wq _ _ _ _ _ _ D A m F hThr hCC K hK hKsub
  obtain ⟨c, hc⟩ := hCC
  obtain ⟨b, hbI, hb⟩ := hNN k r Wp Wq D A m hThr K hK hKsub
  refine ⟨fun p => c * b p, hbI.const_mul c, ?_⟩
  intro u v hu hv hl g hg
  filter_upwards [hb u v hu hv hl g hg, B7.ae_inSS D] with p hp hin
  have hgG : g ∈ GV k r := (hKsub hg).1
  have hsG : sgs p g ∈ GV k r := B7.sgs_mem D hin hgG
  have hN : 0 < gN (sgs p g) := B6.gN_pos hsG
  have hgA : 0 < gN (sgs p g) ^ A := Real.rpow_pos_of_pos hN A
  have hc0 : 0 ≤ c := by
    have h0 := hc.2 [] [] (by simp) (by simp) (by simp) g hgG
    exact le_trans (mul_nonneg (Real.rpow_pos_of_pos (B6.gN_pos hgG) A).le (norm_nonneg _)) h0
  have hall := allLie_ad (sL_mem hin) (sR_mem hin) hu hv
  have hlen : (B4.lr (u.map (AdL p)) (v.map (AdR p))).length ≤ m := by
    rw [B4.length_lr, List.length_map, List.length_map]; exact hl
  have hbd := B4.bound_scaled hc _ (B4.lrt_lr _ _) hall hlen _ hsG
  rw [← B4.dLR_eq, pn_lr] at hbd
  refine (B7.norm_rho_le D hin _ g).trans ?_
  have h1 : ‖dLR (u.map (AdL p)) (v.map (AdR p)) F (sgs p g)‖ ≤
      ((u.map fun X => ‖AdL p X‖).prod * (v.map fun X => ‖AdR p X‖).prod * c) / gN (sgs p g) ^ A := by
    rw [le_div_iff₀ hgA]
    linarith [hbd]
  refine h1.trans (le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left hp hc0))
  rw [Real.rpow_neg hN.le]
  field_simp

end Formalism.FourierDecayAlt.P.JFxDs2
end
end

section

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums

private lemma mul_mem_Nset' {k r : ℕ} {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hA : A ∈ Nset k r) (hB : B ∈ Nset k r) : A * B ∈ Nset k r := by
  obtain ⟨hAu, hAc, hAw⟩ := hA
  obtain ⟨hBu, hBc, hBw⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · have hAu' : Aᴴ * Hpk k r * A = Hpk k r := hAu
    have hBu' : Bᴴ * Hpk k r * B = Hpk k r := hBu
    show (A * B)ᴴ * Hpk k r * (A * B) = Hpk k r
    rw [Matrix.conjTranspose_mul,
      show Bᴴ * Aᴴ * Hpk k r * (A * B) = Bᴴ * (Aᴴ * Hpk k r * A) * B by
        simp only [Matrix.mul_assoc], hAu', hBu']
  · intro a i hai
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hBc a (eI k r a) (le_refl a.val), if_pos rfl, mul_one]
      exact hAc a i hai
    · intro j _ hj
      by_cases hja : a.val ≤ j.val
      · rw [hBc a j hja, if_neg hj, mul_zero]
      · rw [not_le] at hja
        have hjr : j.val < r := lt_trans hja a.isLt
        have h1 := hAc ⟨j.val, hjr⟩ i (show j.val ≤ i.val by omega)
        rw [show eI k r ⟨j.val, hjr⟩ = j from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i j hj1 hj2 hi
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hBw j j hj1 hj2 hj1, if_pos rfl, mul_one]
      exact hAw i j hj1 hj2 hi
    · intro l _ hl
      by_cases hlr : r ≤ l.val
      · rw [hBw l j hj1 hj2 hlr, if_neg hl, mul_zero]
      · rw [not_le] at hlr
        have h1 := hAc ⟨l.val, hlr⟩ i (show l.val ≤ i.val by omega)
        rw [show eI k r ⟨l.val, hlr⟩ = l from Fin.ext rfl] at h1
        rw [h1, if_neg (by rintro rfl; omega), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

private lemma dite_lt_eq_sum_smul_bvec {k r : ℕ} (g : Fin r → ℂ) :
    (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then g ⟨p.val, hp⟩ else 0) =
      ∑ c, g c • bvec (eI k r c) := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, bvec, smul_eq_mul, Pi.single_apply]
  split_ifs with hp
  · rw [Finset.sum_eq_single ⟨p.val, hp⟩]
    · rw [if_pos (show p = eI k r ⟨p.val, hp⟩ from Fin.ext rfl), mul_one]
    · intro c _ hc
      rw [if_neg, mul_zero]
      intro h
      apply hc
      apply Fin.ext
      show c.val = p.val
      rw [h]
      rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  · symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg, mul_zero]
    intro h
    apply hp
    rw [h]
    exact c.isLt

theorem c2_tau_mem : C2.TauMem := by
  intro k r z hz v hv
  set ξ : Fin r → ℂ := fun a => v a.castSucc (Fin.last r) with hξ
  set vX := v.submatrix Fin.castSucc Fin.castSucc with hvX
  have htau : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := rfl
  have hvX_mem : vX ∈ C2.UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hij), fun i => hv.2 _⟩
  have hzW : ∀ i : Fin (2 * r + k + 1), r + k < i.val → z i = 0 := fun i hi => hz.1 i (Or.inr hi)
  have hxi : C2.xiV k r ξ = ∑ c, ξ c • bvec (eI k r c) := by
    rw [← dite_lt_eq_sum_smul_bvec]
    rfl
  have hfc : ∀ c : Fin r, fvec k r z c.castSucc = bvec (eI k r c) := by
    intro c
    simp [fvec]
  have hfl : fvec k r z (Fin.last r) = z := by
    simp [fvec]
  have hact : ∀ b, C2.tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    rw [htau, ← Matrix.mulVec_mulVec, Fin.sum_univ_castSucc]
    simp only [hfc, hfl]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · have hmz : C2.mX k r vX *ᵥ z = z := by
        funext p
        simp only [Matrix.mulVec, dotProduct]
        rw [Finset.sum_eq_single p]
        · by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p p hp.1 hp.2, if_pos rfl, one_mul]
          · have : z p = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro j _ hj
          by_cases hjW : r ≤ j.val ∧ j.val ≤ r + k
          · rw [unipotent_apply_middle_column vX p j hjW.1 hjW.2, if_neg (Ne.symm hj), zero_mul]
          · have : z j = 0 := by
              apply hz.1
              omega
            rw [this, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hfl, hmz, HermitianXiVector.nEich_apply]
      have h1 : herm (Hpk k r) z (C2.xiV k r ξ) = 0 :=
        HermitianXiVector.herm_X_right (C2.xiV k r ξ) z (HermitianXiVector.xiV_X ξ) hzW
      have h2 : herm (Hpk k r) z z = ((-(Tz k r z) : ℝ) : ℂ) := hzz_real z
      have hT : ((Tz k r z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hz.2)
      have hll : v (Fin.last r) (Fin.last r) = 1 := hv.2 _
      rw [h1, h2, hll, one_smul, ← hxi]
      have : ((1 : ℂ) / ((Tz k r z : ℝ) : ℂ)) * (-(((-(Tz k r z) : ℝ) : ℂ))) = 1 := by
        push_cast
        field_simp
      rw [zero_smul, mul_zero, zero_smul, add_zero, add_zero, smul_smul, this, one_smul]
      exact add_comm _ _
    · have hmy : C2.mX k r vX *ᵥ bvec (eI k r b') =
          fun p => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0 := by
        rw [FlagSpanVanishing.mulVec_bvec]
        funext p
        exact mX_col_X vX p b'
      have hyX : ∀ i : Fin (2 * r + k + 1), r ≤ i.val →
          (fun p : Fin (2 * r + k + 1) => if hp : p.val < r then vX ⟨p.val, hp⟩ b' else 0) i = 0 := by
        intro i hi
        simp only
        rw [dite_eq_right (by omega)]
      have h1 := HermitianXiVector.herm_X_left _ z hyX hzW
      have h2 := HermitianXiVector.herm_X_left _ (C2.xiV k r ξ) hyX (HermitianXiVector.xiV_apply_last_block_zero ξ)
      have hlow : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [hfc, hmy, HermitianXiVector.nEich_apply, h1, h2, hlow, zero_smul, add_zero]
      simp only [neg_zero, zero_smul, mul_zero, add_zero, smul_zero]
      exact (dite_lt_eq_sum_smul_bvec (k := k) (fun c => vX c b')).trans rfl
  refine ⟨?_, hact, uMap_eq hz _ v hact⟩
  rw [htau]
  exact mul_mem_Nset' (HermitianXiVector.nEich_mem hz ξ) (mX_mem vX hvX_mem)

end Formalism.FourierDecayAlt.P
end

section

theorem Formalism.FourierDecayAlt.P.stabilizer_pairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs
end

section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem rw_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (B.Mat k r)}
    (hU : IsOpen U) {f₁ f₂ : B.Mat k r → E} (he : ∀ x ∈ U, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f₁ x = B.Rw w f₂ x
  | [], _, x, hx, hxG => he x hx hxG
  | X :: w, hw, x, hx, hxG => by
    show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x
    exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp))
      (rw_congr hU he w (fun Y hY => hw Y (by simp [hY])))

theorem coefficient_vector_locality : CVLocal := by
  intro k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  rw [hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  rw [rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]

end Formalism.FourierDecayAlt.P.CutMP.En
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho

noncomputable section

def nrmW (k r : ℕ) (z a : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (herm (Hpk k r) (SSn.prWv k r z a) (SSn.prWv k r z a)).re

section spec

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def PRhoSpec (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp))
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr ρ) {a | 1 / 4 < nrmW P.k P.r z a}) ∧
  (∀ h ∈ UWset P.k P.r z, ∀ ρ a, Pr ρ (h *ᵥ a) = (π h).comp ((Pr ρ a).comp (π h⁻¹))) ∧
  ∀ a, 0 < nrmW P.k P.r z a →
    (∀ ρ (c : ℂ), c ≠ 0 → Pr ρ (c • a) = Pr ρ a) ∧
    (∀ ρ x y, inner ℂ (Pr ρ a x) y = inner ℂ x (Pr ρ a y)) ∧
    (∀ ρ ρ', (Pr ρ a).comp (Pr ρ' a) = if ρ = ρ' then Pr ρ a else 0) ∧
    ∀ ρ (x : Wp), Pr ρ a x = x ↔
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, SSn.prWv P.k P.r z a] Fr →
        ∀ w : ℂ, Q.capRep P.k P.r π Fr w x = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • x

end spec

def PRhoExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ Pr, PRhoSpec P Bs.z Bs.π Pr

section ctx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Hyp (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  BuiltOW Cc S T f χ ν' m₀ top A₀ ∧ IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

end ctx

def GaugeLines : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k →
    ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ (ρ : M.Ty (D.parOf S v))
      (Fr : Fin (S.G.k - 1) → Fin (2 * S.G.r + S.G.k + 1) → ℂ),
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z, SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ] Fr →
      ∀ (w : ℂ) (x : Wq (S.pl v)),
        Q.capRep S.G.k S.G.r (T v).base.π Fr w (e ρ ζ x) =
          M.xC (D.parOf S v) ρ (w - ((S.G.k : ℂ) - 2) / 2) • e ρ ζ x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.B

theorem lemma_B_of_components : Formalism.FourierDecayAlt.B.LemmaB :=
  bessel_lemma_from_reductions bilinear_form_continuity ae_equality_from_test_functions fatou_lemma_in_parameter matrix_coefficient_linear dilation_matrix_coefficient
    bessel_function_trivial_index regularized_beta_bound_continuity_sesquilinear regularised_average_identity unfolding_identity_of_integration_formula orbital_integral_ae_convergence_continuity
    dilation_identity_of_jacobian phase_function_adjoint regularised_pairing_via_phase assemble_equality_identity adjointness_of_bessel_transform

theorem b_lemmaBClosed_of : Formalism.FourierDecayAlt.B.XiExists → Formalism.FourierDecayAlt.B.LemmaBClosed := fun hX =>
  bessel_lemma_closed_form hX lemma_B_of_components clause_of_regularized_limit adjointness_polynomially_bounded

end Formalism.FourierDecayAlt.P
end
