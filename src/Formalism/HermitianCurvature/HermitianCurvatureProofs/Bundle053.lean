module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.IsUnitDetOfMemGV
public import Formalism.HermitianCurvature.OperatorsCommuteTranslations
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.PRowWSColW
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.HermitianOrthogonalProjectionVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormFormOneUnitary.UnitaryP
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
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

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants

noncomputable section

section N2

variable {k r : ℕ}

theorem sg_esI (b : Fin r) : NFOne.sg k r (esI k r b) = eI k r b := by
  have hb := b.isLt
  ext
  simp only [NFOne.sg, esI, eI]
  omega

theorem pm_col_star (j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (b : Fin r) (hb : b.val < j) :
    (1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b) = V b.val := by
  funext p
  have hb' := b.isLt
  have hq : r + k < (esI k r b).val := by simp only [esI]; omega
  have hsg : (NFOne.sg k r (esI k r b)).val = b.val := by rw [sg_esI]; rfl
  have hcol : ((1 + NFOne.Pm k r j V) *ᵥ bvec (esI k r b)) p =
      (if p = esI k r b then 1 else 0) + NFOne.Pm k r j V p (esI k r b) := by
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.add_apply, Matrix.one_apply, add_mul]
  rw [hcol]
  by_cases hp1 : p.val < r
  · rw [NFOne.P_XS k r j V p _ hp1 hq, hsg, if_pos hb, if_neg (fun e => by rw [e] at hp1; omega), zero_add]
  · by_cases hp2 : p.val ≤ r + k
    · rw [NFOne.P_WS k r j V p _ (by omega) hp2 hq, hsg, if_neg (fun e => by rw [e] at hp2; omega), zero_add]
    · rw [NFOne.P_rowS k r j V p _ (by omega), add_zero, Vs b.val hb p (by omega)]
      have e : p = esI k r b ↔ (NFOne.sg k r p).val = b.val := by
        rw [Fin.ext_iff]; simp only [NFOne.sg, esI]; omega
      by_cases h1 : p = esI k r b
      · rw [if_pos h1, if_pos (e.mp h1)]
      · rw [if_neg h1, if_neg (fun h2 => h1 (e.mpr h2))]

theorem one_add_projection_mem_isotropic_set (j : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val → V b q = if (NFOne.sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0)
    (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + NFOne.Pm k r j V) ∈ N0set k r z' := by
  refine ⟨NFOne.unitary_P k r j V V0 Vs Viso, fun a => NFOne.cols_X k r j V a,
    NFOne.z_fix k r j V z' hz Vz, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · rw [Matrix.add_apply, NFOne.P_rowWS_colW k r j V p q hp hq2, add_zero, Matrix.one_apply]
  · rw [Matrix.add_apply, NFOne.P_rowS k r j V p q hp, add_zero, Matrix.one_apply]

private theorem mul_mem_n0set {z' : Fin (2 * r + k + 1) → ℂ}
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ N0set k r z') (hh : h ∈ N0set k r z') :
    g * h ∈ N0set k r z' := by
  obtain ⟨gU, gX, gz, gW, gS⟩ := hg
  obtain ⟨hU, hX, hz, hW, hS⟩ := hh

  have col : ∀ p m : Fin (2 * r + k + 1), m.val < r → g p m = if p = m then 1 else 0 := by
    intro p m hm
    have := congrFun (gX ⟨m.val, hm⟩) p
    simpa [bvec, eI, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have key : ∀ p q : Fin (2 * r + k + 1), r ≤ p.val →
      ((r ≤ q.val ∧ q.val ≤ r + k) ∨ (r + k < q.val ∧ r + k < p.val)) →
      ∀ m, g p m * h m q = if m = q then g p q else 0 := by
    intro p q hp hq m
    have hqr : r ≤ q.val := by rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
    by_cases hm1 : m.val < r
    · rw [col p m hm1, if_neg (fun e => by rw [e] at hp; omega), zero_mul,
        if_neg (fun e => by rw [e] at hm1; omega)]
    · have tail : h m q = (if m = q then 1 else 0) → g p m * h m q = if m = q then g p q else 0 := by
        intro hmq
        by_cases e : m = q
        · subst e; simp [hmq]
        · simp [hmq, e]
      by_cases hm2 : m.val ≤ r + k
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · rw [gW p m (by omega) hm2 hp, if_neg (fun e => by rw [e] at hp2; omega), zero_mul,
            if_neg (fun e => by rw [e] at hm2; omega)]
      · rcases hq with ⟨hq1, hq2⟩ | ⟨hq1, hp2⟩
        · exact tail (hW m q hq1 hq2 (by omega))
        · exact tail (hS m q hq1 (by omega))
  refine ⟨?_, fun a => ?_, ?_, fun p q hq1 hq2 hp => ?_, fun p q hq hp => ?_⟩
  · change (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
    change gᴴ * Hpk k r * g = Hpk k r at gU
    change hᴴ * Hpk k r * h = Hpk k r at hU
    rw [Matrix.conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [Matrix.mul_assoc], gU, hU]
  · rw [← Matrix.mulVec_mulVec, hX, gX]
  · rw [← Matrix.mulVec_mulVec, hz, gz]
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q hp (Or.inl ⟨hq1, hq2⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gW p q hq1 hq2 hp
  · rw [Matrix.mul_apply, Finset.sum_congr rfl (fun m _ => key p q (by omega) (Or.inr ⟨hq, hp⟩) m),
      Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    exact gS p q hq hp

theorem mul_mem_isotropic_unipotent_set (z' : Fin (2 * r + k + 1) → ℂ) (j1 j2 : ℕ) (V1 V2 : ℕ → Fin (2 * r + k + 1) → ℂ)
    (h1 : (1 + NFOne.Pm k r j1 V1) ∈ N0set k r z') (h2 : (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z') :
    (1 + NFOne.Pm k r j1 V1) * (1 + NFOne.Pm k r j2 V2) ∈ N0set k r z' := by
  exact mul_mem_n0set h1 h2

theorem herm_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) v (bvec (esI k r b)) = v (eI k r b) := by
  apply PI.StabPairsW.herm_es <;> assumption

end N2

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def omT (p : KB.Pl P Wp Wq) (N : ℕ) (Q : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(Top.wPt (TBB.TTp p) P.r Q ^ N)

end place

def ptT (s : ℕ) (h : C.LPt) (x D : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]
  | some u => h ++ [(s, u)]

def coT (s : ℕ) (x : ℂ) : Option ℂ → ℂ
  | none => ((‖x‖ ^ (s - 1) : ℝ) : ℂ)
  | some u => -(G.psi U.betaU ((s : ℂ) * u * x) * ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ))

def epsT (s : ℕ) : ℂ := (-1) ^ (s + 1)

def TopGram1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → (∀ y, 0 < nn y) →
    ∃ (I : Type) (_ : Fintype I) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (L : I → (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      (∀ i, 0 ≤ c i) ∧ (∀ i, KB.CptCoef p.T.base (Fi i)) ∧
      ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
        ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'),
          (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ

def TopCore1 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
      ‖∑ j ∈ Finset.insertNone (G.rootSet s (epsT s * D)), (coT s x j * (omT p N (ptT s h x D j) : ℂ)) •
          p.V F' (ptT s h x D j)‖ ≤ C * ‖x‖⁻¹

def YCont : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base F' →
    ∀ (N m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
      ContinuousOn (fun c : ℂ => (omT p N (h ++ [(m, c)]) : ℂ) • p.V F' (h ++ [(m, c)])) {0}ᶜ

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.GLG

open Formalism.FourierDecayAlt

noncomputable section

theorem zpow_two_nat (x : ℝ) (e : ℤ) (n : ℕ) (he : e = 2 * (n : ℤ)) : x ^ e = (x ^ n) ^ 2 := by
  subst he
  rw [show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']

theorem nPt_block {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (t c : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 1, t), (1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h *
        ((‖t‖ ^ ((m + 1) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m))) ^ 2 *
          (‖c‖ ^ (U.Mlev P.k (P.r - (b + (m + 2) - 1)) - 2)) ^ 2) := by
  have e : h ++ [(m + 1, t), (1, c)] = (h ++ [(m + 1, t)]) ++ [(1, c)] := by simp
  have hs1 : D.ptSize (h ++ [(m + 1, t)]) = b - 1 + (m + 1) := by
    simp only [D.ptSize, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hh ⊢
    omega
  unfold TBB.nPt
  rw [e, PBD.weight_product_append, PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hs1, hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega), if_neg (by omega), mul_assoc]
  congr 2
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1) + (m + 1) - 1 = b + m := by omega
    rw [e1]
    push_cast [Nat.cast_sub (show b + (m + 2) - 1 ≤ P.r from hi), Nat.cast_sub (show b + m ≤ P.r + 1 by omega)]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring
  · apply zpow_two_nat
    unfold C.Mlev U.Mlev
    have e1 : 1 + (b - 1 + (m + 1)) + 1 - 1 = b + (m + 2) - 1 := by omega
    rw [e1]
    have h3 : 2 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 := by omega
    push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
    rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
    push_cast
    ring

theorem nPt_long {P : M.Par} (TT : ℝ) (b m : ℕ) (hb : 1 ≤ b) (hi : b + (m + 2) - 1 ≤ P.r) (h : C.LPt)
    (hh : D.ptSize h = b - 1) (z : ℂ) :
    TBB.nPt P.k P.r TT (h ++ [(m + 2, z)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 h * (‖z‖ ^ ((m + 2) * (U.Mlev P.k (P.r - (b + (m + 2) - 1)) + m - 1))) ^ 2 := by
  unfold TBB.nPt
  rw [PBD.weight_product_append, PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 _ h 1 le_rfl (by omega), hh]
  simp only [C.nAux, one_mul, mul_one]
  rw [if_neg (by omega)]
  congr 1
  apply zpow_two_nat
  unfold C.Mlev U.Mlev
  have e1 : 1 + (b - 1) + (m + 2) - 1 = b + (m + 2) - 1 := by omega
  rw [e1]
  have h3 : 1 ≤ P.k + 2 * (P.r - (b + (m + 2) - 1)) + 3 + m := by omega
  push_cast [Nat.cast_sub h3, Nat.cast_sub hi]
  rw [Nat.cast_sub (show 1 ≤ b + (m + 2) by omega)]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutBP.GLG
end

section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

theorem isBoundedBilinearMap_compR {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] :
    IsBoundedBilinearMap ℝ (fun q : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wq) => q.1.comp q.2) :=
  ((ContinuousLinearMap.compL ℂ Wq Wq Wp).bilinearRestrictScalars ℝ).isBoundedBilinearMap


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem ckOn_comp {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {f : B.Mat k r → (Wq →L[ℂ] Wp)}
    {A : B.Mat k r → (Wq →L[ℂ] Wq)} (hf : B.CkOn ⊤ (B.GV k r) f) (hA : B.CkOn ⊤ (B.GV k r) A) :
    B.CkOn ⊤ (B.GV k r) (fun g => (f g).comp (A g)) := by
  intro g₀ hg₀
  obtain ⟨U1, f1, hU1, h1, hc1, he1⟩ := hf g₀ hg₀
  obtain ⟨U2, A1, hU2, h2, hc2, he2⟩ := hA g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => (f1 g).comp (A1 g), hU1.inter hU2, ⟨h1, h2⟩, ?_, ?_⟩
  · exact isBoundedBilinearMap_compR.contDiff.comp_contDiffOn
      ((hc1.mono Set.inter_subset_left).prodMk (hc2.mono Set.inter_subset_right))
  · intro x hx hxG
    simp only [he1 x hx.1 hxG, he2 x hx.2 hxG]

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

section fpm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end fpm

def LimE (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (N : ℕ) : Prop :=
  ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
    Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
      (𝓝 (sz * (B.beta p.T.base F F).re))

def LemB (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (κ₀ : ℝ) : Prop :=
  ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F

def Amaps (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Ap Am : B.Mat P.k P.r → (Wq →L[ℂ] Wq))
    (ApPt AmPt : C.LPt → (Wq →L[ℂ] Wq)) (b : ℝ) (n₀ : ℕ) : Prop :=
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Ap g)) γ = (p.V f γ).comp (ApPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
      p.V (fun g => (f g).comp (Am g)) γ = (p.V f γ).comp (AmPt γ)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ∀ v : Wq,
      ‖v‖ ^ 2 ≤ (3 * b) ^ (2 * n₀) * (TBB.Tq p / TBB.Gp p γ) ^ n₀ *
        (‖(ContinuousLinearMap.adjoint (ApPt γ)) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint (AmPt γ)) v‖ ^ 2)) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖ApPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀) ∧
  (∀ γ, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ → ‖AmPt γ‖ ^ 2 ≤ (TBB.Gp p γ / TBB.Tq p) ^ n₀)

def BigCellDerivativeExpansion (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) : Prop :=
  ∀ a, a ≤ a₁ → ∃ (n : ℕ) (fi : Fin n → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (co : Fin n → ℂ),
    ∑ i, ‖co i‖ ≤ b ^ (C₃ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2 * (a : ℝ)) ∧
    (∀ i, TBB.jN2 p (fi i) ≤ TBB.jN2 p f) ∧
    (∀ i, AEMeasurable fun c : Fin (P.r + 1) → ℂ =>
      ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fi i) (P.r + 1) [] (TBB.bigPt P.r c))) ∧
    ∀ c : Fin (P.r + 1) → ℂ, D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ((D.ptMatN (TBB.bigPt P.r c) (P.r + 1)).det ^ a) • p.V f (TBB.bigPt P.r c) =
        ∑ i, co i • p.V (fi i) (TBB.bigPt P.r c)

end place

end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem ptSize_toStd (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P := by
  intro b P
  induction P generalizing b with
  | nil => rfl
  | cons block rest ih =>
    obtain ⟨s, t⟩ := block
    simpa only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] using congrArg (s + ·) (ih (b + s))

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lamP (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (i : ℕ) (P : C.LPt) : ℝ :=
  √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) /
    (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
      √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i * S.sizeAt v a))

end defs

def GNSetC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i),
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q))

def GermConst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b s : ℕ), 0 < S.G.g1 → 0 < S.G.g2 →
    1 ≤ b → 2 ≤ s → b + s - 1 ≤ S.G.r → ∀ h : C.LPt, D.ptSize h = b - 1 →
    ∃ μ₀ : ℝ, ∀ x D z : ℂ, x ≠ 0 → D ≠ 0 → z ^ s = D →
      (‖x‖ ^ (s - 1) * (√(KB.dlB S (b + s - 1) 1))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]) *
          kapB (s - 2) =
        μ₀ * ((‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ (s - 1))⁻¹ *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ ((s - 1) * (U.Mlev S.G.k (S.G.r - (b + s - 1)) + (s - 2))) *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2))) ∧
      ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s, z)]) *
          Real.pi ^ (s * (s - 1) / 2) =
        μ₀ * (‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D) *
            GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹ ^ (s - 1)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2) *
          ((s : ℝ)⁻¹ * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b s z‖ ^ ((s - 1) ^ 2)))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def YGSlice : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h' : C.LPt) (m ρ : ℕ)
    (e1 : r = D.ptSize h' + (m + 2) + ρ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ : G.Mat (m + 2) → V) (L : V →L[ℂ] E) (γ : B.Mat k ρ) (Kc : Set ℂ) (K a : ℝ),
    D.IsLocPt h' (D.ptSize h') → (0 : ℂ) ∉ Kc → ((m : ℝ) + 1) * ((m : ℝ) + 4) < a →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → G.detM Z ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc →
      L (Φ Z) = U.PhiFun k ρ (D.ptPerm h') (D.ptDiag h') (D.castV e1 z) (D.castV e1 z')
        (D.castF e1.symm F) Z γ) →
    ∀ q, okG m Kc q →
    Integrable (fun ξ : U.Xi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) =>
        U.psiStar k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.castV (by rw [ptSize_ptG]; omega) z)
          (D.castV (by rw [ptSize_ptG]; omega) z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) F
            (U.gaXi k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
      (U.muXi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) →
    L (yG U.betaU m Φ q) = D.sliceAt k r z z' F (ptG h' m q) (D.castM (by rw [ptSize_ptG]; omega) γ)

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end
