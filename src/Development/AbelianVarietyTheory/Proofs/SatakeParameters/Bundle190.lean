module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle164
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle186
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle185
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle187
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

section

noncomputable section
namespace GlobalTheory.Hk3.HoweDuality

theorem exists_int_gram_of_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan x hw
  obtain ⟨hne, hfx⟩ := GlobalTheory.T.heisenbergTranslate_fixed_integralUnitary L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs x hw
  have Hph : ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1 := by
    intro h hh hint
    have e := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hs _ hint, add_sub_cancel, hfx h hh hint] at e
    have e2 : (ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) - 1) • ρ x s = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hne
  exact GlobalTheory.T.exists_integral_gram_of_phase_conditions L ϖ σ q δ n n' JS ψ hP.unr hP.odd hP.intS hP.hermS hP.delta hP.psi_int hP.psi_ne x
    (GlobalTheory.T.cayleyTransform_trivial_phase_skewHermitian L ϖ σ q δ n n' JS JT ψ hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT hP.delta hP.psi_int x Hph)
end GlobalTheory.Hk3.HoweDuality
end
end

section

noncomputable section

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem pi_int {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : Formalism.UG.IsUnramInv ϖ σ q) : ϖ ∈ Formalism.UG.intL L := by
  show Valued.v ϖ ≤ 1
  rw [hU.2.2.2.1]
  exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)

theorem glint_entry {n : ℕ} {h : GL (Fin n) L} (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) (r s : Fin n) :
    (h : Matrix (Fin n) (Fin n) L) r s ∈ Formalism.UG.intL L := by
  obtain ⟨g0, hg0⟩ := hh
  rw [← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) r s).2

theorem mulVec_int {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : (M *ᵥ v) r ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun s _ => (Formalism.UG.intL L).mul_mem (hM r s) (hv s)

theorem dvdPow_mulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, DvdPow ϖ k (M r s))
    {v : Fin n → L} (hv : ∀ r, v r ∈ Formalism.UG.intL L) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  refine dvdPow_sum _ _ fun s _ => ?_
  rw [mul_comm]; exact dvdPow_mul_int (hM r s) (hv s)

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) :
    Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_unitary (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (h : Formalism.UG.UJ σ J) (x y : Fin n → L) :
    Formalism.UG.hform σ J (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ x)
      (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ y) = Formalism.UG.hform σ J x y := by
  have hu : Formalism.UG.cT σ ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * J * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = J := h.2
  rw [hform_eq_dot, hform_eq_dot]
  set H := ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have e1 : (fun i => σ ((H *ᵥ x) i)) = (H.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i; exact RingHom.map_mulVec σ H x i
  rw [e1, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  exact congrArg (· *ᵥ y) hu

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_intMulVec {ϖ : L} {k : ℕ} {n : ℕ} {M : Matrix (Fin n) (Fin n) L} (hM : ∀ r s, M r s ∈ Formalism.UG.intL L)
    {v : Fin n → L} (hv : ∀ r, DvdPow ϖ k (v r)) (r : Fin n) : DvdPow ϖ k ((M *ᵥ v) r) := by
  simp only [Matrix.mulVec, dotProduct]
  exact dvdPow_sum _ _ fun s _ => dvdPow_mul_int (hv s) (hM r s)

theorem indepMod_mulVec {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {h : GL (Fin n) L}
    (hh : h ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L)) {z : ι → Fin n → L} (hz : IndepMod ϖ z) :
    IndepMod ϖ (fun i => (h : Matrix (Fin n) (Fin n) L) *ᵥ z i) := by
  intro d hd hs i
  refine hz d hd (fun r => ?_) i
  set w : Fin n → L := ∑ j, d j • z j with hw
  have e1 : ∀ s, ((h : Matrix (Fin n) (Fin n) L) *ᵥ w) s = ∑ j, d j * ((h : Matrix (Fin n) (Fin n) L) *ᵥ z j) s := by
    intro s
    simp [hw, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]
  have e2 : ∑ j, d j * z j r = (((h⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ ((h : Matrix (Fin n) (Fin n) L) *ᵥ w)) r := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    simp [hw, Finset.sum_apply]
  rw [e2]
  exact dvdPow_intMulVec (glint_entry ((Formalism.UG.GLint _ _).inv_mem hh)) (fun s => by rw [e1]; exact hs s) r

theorem indepMod_sub {ϖ : L} {ι : Type} [Fintype ι] {n : ℕ} {z : ι → Fin n → L} (hz : IndepMod ϖ z)
    (p : ι → Prop) [DecidablePred p] : IndepMod ϖ (fun i : {i // p i} => z i.1) := by
  intro d hd hs i
  let d' : ι → L := fun j => if hj : p j then d ⟨j, hj⟩ else 0
  have h1 : ∀ j, d' j ∈ Formalism.UG.intL L := by
    intro j; by_cases hj : p j
    · simp only [d', dif_pos hj]; exact hd _
    · simp only [d', dif_neg hj]; exact (Formalism.UG.intL L).zero_mem
  have h2 : ∀ r, ∑ j, d' j * z j r = ∑ j : {i // p i}, d j * z j.1 r := by
    intro r
    rw [← Fintype.sum_subtype_add_sum_subtype p (fun j => d' j * z j r)]
    have a1 : ∑ j : {i // ¬ p i}, d' j.1 * z j.1 r = 0 :=
      Finset.sum_eq_zero fun j _ => by simp [d', dif_neg j.2]
    rw [a1, add_zero]
    exact Finset.sum_congr rfl fun j _ => by simp [d', dif_pos j.2]
  have := hz d' h1 (fun r => by rw [h2]; exact hs r) i.1
  simpa [d', dif_pos i.2] using this

end GlobalTheory.Hk3.IntWittMod

namespace GlobalTheory.Hk3.IntWittMod

open Matrix GlobalTheory.Hk3.IntWitt

theorem witt_mod_pow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n' : ℕ) (JT : GL (Fin n') L),
    JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ (ι : Type) [Fintype ι] (a : ι → ℕ) (z z' : ι → Fin n' → L), (∀ i, 1 ≤ a i) →
    (∀ i r, z i r ∈ Formalism.UG.intL L) → (∀ i r, z' i r ∈ Formalism.UG.intL L) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ z → GlobalTheory.Hk3.IntWitt.IndepMod ϖ z' →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (min (a i) (a j)) (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z' i) (z' j) - Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (z i) (z j))) →
    ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a i) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
  intro L _ _ _ ϖ σ q hU hq n' JT hJT hJh ι _ a z z' ha hz hz' hiz hiz' hG
  classical
  have hϖ := pi_int hU
  have key : ∀ k, 1 ≤ k → ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
      (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
      ∀ i r, DvdPow ϖ (min (a i) k) ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      obtain ⟨h, hh, hc⟩ := GlobalTheory.T.integral_witt_unitary_mod_uniformizer L ϖ σ q hU hq n' JT hJT hJh ι z z' hz hz' hiz hiz'
        (fun i j => dvdPow_mono hϖ (le_min (ha i) (ha j)) (hG i j))
      refine ⟨h, hh, fun i r => ?_⟩
      rw [min_eq_right (ha i)]; exact hc i r
    | succ k hk ih =>
      obtain ⟨h, hh, hc⟩ := ih
      have hHint := glint_entry hh
      obtain ⟨g, hg, hg1, hgc⟩ := GlobalTheory.T.unitaryGroup_hensel_step_families L ϖ σ q hU hq n' JT hJT hJh {i // k < a i}
        (fun i => ((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i.1) (fun i => z' i.1) k hk
        (fun i r => mulVec_int hHint (hz i.1) r) (fun i r => hz' i.1 r)
        (indepMod_sub (indepMod_mulVec hh hiz) (fun i => k < a i))
        (fun i r => by
          have h0 := hc i.1 r
          rw [min_eq_right i.2.le] at h0
          have h1 := dvdPow_neg h0
          rwa [neg_sub] at h1)
        (fun i j => by
          simp only [hform_unitary]
          exact dvdPow_mono hϖ (le_min i.2 j.2) (hG i.1 j.1))
      refine ⟨g * h, (Formalism.UG.GLint _ _).mul_mem hg hh, fun i r => ?_⟩
      have e : (((g * h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i
          = ((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) := by
        simp [Matrix.mulVec_mulVec]
      rw [e]
      by_cases hki : k < a i
      · rw [min_eq_right (Nat.succ_le_of_lt hki)]
        exact hgc ⟨i, hki⟩ r
      · push_neg at hki
        rw [min_eq_left (by omega)]
        have h2 := hc i r
        rw [min_eq_left hki] at h2
        have h1 : DvdPow ϖ (a i) (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
            (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r) :=
          dvdPow_mono hϖ hki (dvdPow_mulVec (fun r s => by simpa [Matrix.sub_apply] using hg1 r s)
            (mulVec_int hHint (hz i)) r)
        have e2 : (((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r - z' i r
            = (((((g : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) - 1) *ᵥ
              (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i)) r)
              + ((((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ z i) r - z' i r) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]; ring
        rw [e2]; exact dvdPow_add h1 h2
  obtain ⟨h, hh, hc⟩ := key (1 + ∑ i, a i) (by omega)
  refine ⟨h, hh, fun i r => ?_⟩
  have h0 := hc i r
  have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
  rwa [min_eq_left (by omega)] at h0

end GlobalTheory.Hk3.IntWittMod

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ (k : D.what₂.Tau × Fin N' × Fin N) (z : Bool × HH D) (a : Fin N) (b₀ : Fin N'), ∑ i, Formalism.L2.KerInert.RepFrame.lamB D lam b k i * ((gK D lam P P' b z a b₀ i : MaximalUnramifiedExtension p) : ℂ_[p]) = chgB D lam P P' k ((0 : ZMod 1), (tauPl D z, a, b₀)) := by
  first | exact @GlobalTheory.KerStd.HypCoord.lamB_sum_gK | exact GlobalTheory.KerStd.HypCoord.lamB_sum_gK | (intros; apply GlobalTheory.KerStd.HypCoord.lamB_sum_gK <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem comb_of_scalar {X A M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s) (cA : A →₀ ℂ) :
    ∃ C : X →₀ ℂ, ∀ s, vac s → (cA.sum fun p z => z • a p s) = C.sum fun x z => z • r x s := by
  choose ca hca using ha
  refine ⟨Finsupp.linearCombination ℂ ca cA, fun s hs => ?_⟩
  have h : Finsupp.linearCombination ℂ (fun x => r x s) (Finsupp.linearCombination ℂ ca cA) =
      Finsupp.linearCombination ℂ (fun p => a p s) cA := by
    rw [LinearMap.map_finsupp_linearCombination]
    congr 2
    funext p
    exact (Finsupp.linearCombination_apply ℂ (ca p)).trans (hca p s hs).symm
  calc (cA.sum fun p z => z • a p s) = Finsupp.linearCombination ℂ (fun p => a p s) cA :=
        (Finsupp.linearCombination_apply ℂ cA).symm
    _ = _ := h.symm
    _ = _ := Finsupp.linearCombination_apply ℂ _

theorem comb_transfer {X A B M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (b : B → Module.End ℂ M)
    (hmodel : ∀ c : X →₀ ℂ, ∀ s, s ≠ 0 → vac s → (c.sum fun x z => z • r x s) = 0 →
      ∀ s', vac s' → (c.sum fun x z => z • r x s') = 0)
    (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s)
    (hb : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → b p s = c.sum fun x z => z • r x s)
    (cA : A →₀ ℂ) (cB : B →₀ ℂ) (s0 : M) (h0 : s0 ≠ 0) (hv : vac s0)
    (heq : (cA.sum fun p z => z • a p s0) = cB.sum fun p z => z • b p s0) :
    ∀ s, vac s → (cA.sum fun p z => z • a p s) = cB.sum fun p z => z • b p s := by
  obtain ⟨CA, hA⟩ := comb_of_scalar vac r a ha cA
  obtain ⟨CB, hB⟩ := comb_of_scalar vac r b hb cB
  have hsub : ∀ s, ((CA - CB).sum fun x z => z • r x s) =
      (CA.sum fun x z => z • r x s) - CB.sum fun x z => z • r x s := by
    intro s
    have e : ∀ C : X →₀ ℂ, (C.sum fun x z => z • r x s) = Finsupp.linearCombination ℂ (fun x => r x s) C :=
      fun C => (Finsupp.linearCombination_apply ℂ C).symm
    rw [e, e, e, map_sub]
  have h0' : ((CA - CB).sum fun x z => z • r x s0) = 0 := by
    rw [hsub, ← hA _ hv, ← hB _ hv, heq, sub_self]
  intro s hs
  have h := hmodel (CA - CB) s0 h0 hv h0' s hs
  rw [hsub, sub_eq_zero, ← hA s hs, ← hB s hs] at h
  exact h

theorem howe_on_span (hH : HoweUnram) {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
    {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}
    (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (s0 : M) (h0 : s0 ≠ 0) (hv : LocVac ρ s0) :
    (∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s0)) ∧
    ∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s0) := by
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  set M0 := Submodule.span ℂ (Set.range fun x => ρ x s0) with hM0
  have hs0 : s0 ∈ M0 := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp [hp.rho_zero]
  have hρ : ∀ x, ∀ m ∈ M0, ρ x m ∈ M0 := by
    intro x m hm
    have hle : M0 ≤ M0.comap (ρ x) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ρ x (ρ y s0) = (ρ x * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.rho_mul x y]
      exact M0.smul_mem _ (Submodule.subset_span ⟨x + y, rfl⟩)
    exact hle hm
  have hω : ∀ p, ∀ m ∈ M0, ω p m ∈ M0 := by
    rintro ⟨g, h⟩ m hm
    have hle : M0 ≤ M0.comap (ω (g, h)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ω (g, h) (ρ y s0) = (ω (g, h) * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.norm g h y]
      refine hρ _ _ ?_
      obtain ⟨c, hc⟩ := scal (g, h)
      rw [hc s0 hv]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨c, rfl⟩
    exact hle hm
  let ρ0 : Matrix (Fin n') (Fin n) L → Module.End ℂ M0 := fun x => (ρ x).restrict (hρ x)
  let ω0 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M0 :=
    { toFun := fun p => (ω p).restrict (hω p)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro p p'
        ext m
        simp }
  have ρ0_val : ∀ x (m : M0), ((ρ0 x m : M0) : M) = ρ x m := fun _ _ => rfl
  have ω0_val : ∀ p (m : M0), ((ω0 p m : M0) : M) = ω p m := fun _ _ => rfl
  let t0 : M0 := ⟨s0, hs0⟩
  have hv0 : LocVac ρ0 t0 := fun u hu => Subtype.ext (hv u hu)
  have ht0 : t0 ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hspan : Submodule.span ℂ (Set.range fun x => ρ0 x t0) = ⊤ := by
    have e : (Set.range fun x => ρ0 x t0) = (Subtype.val ⁻¹' (Set.range fun x => ρ x s0) : Set M0) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hp0 : LocPair ϖ σ q δ JS JT ψ ρ0 ω0 :=
    { unr := hp.unr
      odd := hp.odd
      intS := hp.intS
      intT := hp.intT
      hermS := hp.hermS
      hermT := hp.hermT
      delta := hp.delta
      psi_int := hp.psi_int
      psi_ne := hp.psi_ne
      rho_zero := by
        ext m
        simp [ρ0, hp.rho_zero]
      rho_mul := by
        intro x y
        ext m
        have h := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.rho_mul x y)
        exact h
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, t0, hv0, rfl⟩
      norm := by
        intro g h x
        ext m
        have e := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.norm g h x)
        exact e
      fix := by
        intro g h hg hh s hs
        exact Subtype.ext (hp.fix g h hg hh s (fun u hu => congrArg Subtype.val (hs u hu))) }
  obtain ⟨h1, h2⟩ := hH L ϖ σ q δ n n' JS JT ψ M0 ρ0 ω0 hp0 t0 ht0 hv0 hspan
  constructor
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h1 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h2 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

theorem howe_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  intro hH L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have scal := GlobalTheory.T.unramifiedLocalPair_acts_on_vacua_by_heisenberg_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  have model := GlobalTheory.T.locPair_vacuum_relation_independent L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  by_cases hz : ∃ s0 : M, s0 ≠ 0 ∧ LocVac ρ s0
  · obtain ⟨s0, h0, hv⟩ := hz
    obtain ⟨hA, hB⟩ := howe_on_span hH hp s0 h0 hv
    refine ⟨fun cT hT => ?_, fun cS hS => ?_⟩
    · have hw : (cT.sum fun b z => z • ω (1, b) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun b => ω (1, b)) (fun b => scal (1, b)) cT
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cS, hcS⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hB _ hw (hT s0 hv))
      exact ⟨cS, comb_transfer (LocVac ρ) ρ (fun b => ω (1, b)) (fun a => ω (a, 1)) model
        (fun b => scal (1, b)) (fun a => scal (a, 1)) cT cS s0 h0 hv hcS.symm⟩
    · have hw : (cS.sum fun a z => z • ω (a, 1) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun a => ω (a, 1)) (fun a => scal (a, 1)) cS
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cT, hcT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hA _ hw (hS s0 hv))
      exact ⟨cT, comb_transfer (LocVac ρ) ρ (fun a => ω (a, 1)) (fun b => ω (1, b)) model
        (fun a => scal (a, 1)) (fun b => scal (1, b)) cS cT s0 h0 hv hcT.symm⟩
  · have hz' : ∀ s, LocVac ρ s → s = 0 := by
      intro s hs
      by_contra hne
      exact hz ⟨s, hne, hs⟩
    refine ⟨fun cT _ => ⟨0, fun s hs => ?_⟩, fun cS _ => ⟨0, fun s hs => ?_⟩⟩
    · simp [hz' s hs, Finsupp.sum]
    · simp [hz' s hs, Finsupp.sum]

end GlobalTheory.Hk3

end
end

section

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.kernelBasis_determinant_abs_at_place : ∀ (D : D7) (Dx : DivX D) (Tw : TwForms D) (E : KerEnt D Dx Tw) (u : D.what₂.Word) (μ : D.what₂.Tup) (O : GL3Theta.LiftObj D (D.chTw u μ)) (w : D.what₂.places.Pl) (T : GL3Columns.KFTie E O w), T.detB := by
  first | exact @GlobalTheory.SatakeUnitDeterminantBasis.detB | exact GlobalTheory.SatakeUnitDeterminantBasis.detB | (intros; apply GlobalTheory.SatakeUnitDeterminantBasis.detB <;> assumption)
end
