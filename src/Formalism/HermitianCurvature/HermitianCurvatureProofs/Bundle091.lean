module

public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle084
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩

theorem prod_Icc_one (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]
    simp

abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩

theorem rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by
  have h1 := hL j.castSucc
  have h2 := hL j.succ
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  have hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) =
      ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ) := by
    simp only [M.Par.hi, M.Par.lo, par, min_self, max_self]
    push_cast
    linarith
  have hnn : 0 ≤ L j.castSucc - L j.succ - 1 := by linarith [hg j]
  simp only [M.Par.wid]
  rw [hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]

theorem main (hK : BranchingK) (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (hOK : (par n r T T' u).OK)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (hz : inWb (n + 1) r z)
    (hT : 0 < Tz (n + 1) r z) (hπ : IsType (n + 1) r z π u) (he : inWb (n + 1) r e)
    (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1) :
    ∃ S : M.Ty (par n r T T' u) → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (ρ : M.Ty (par n r T T' u)) (w : ℂ), ∀ v ∈ S ρ,
        capRep (n + 1) r π Bs w v = M.xC (par n r T T' u) ρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • v := by
  have hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ) := fun j =>
    hOK.int_u ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1
        omega)
  choose L hL using hint
  have hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1) := fun j => by
    have h := hOK.gap ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1 - 1
        omega)
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at h
    linarith
  have hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc := fun j => by
    have h1 := hL j.castSucc
    have h2 := hL j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have : (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega
  have hw := wid_eq n r T T' u L hL hg
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)
    rw [hβ, ← h]
    ring
  obtain ⟨S₀, hint₀, hirr, heig⟩ := hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee
  let Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M} := fun ρ =>
    ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by
      have h1 := (ρ j).2
      have h2 := hw j
      constructor
      · show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)
        omega
      · show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc
        omega⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro ρ ρ' h
      funext j
      have h1 := congrFun (congrArg Subtype.val h) j
      simp only [Φ] at h1
      apply Fin.ext
      omega
    · intro M
      refine ⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩
      · have h1 := M.2 j
        have h2 := hw j
        omega
      · apply Subtype.ext
        funext j
        have h1 := M.2 j
        simp only [Φ]
        omega
  refine ⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩
  intro Bs hBs ρ w v hv
  rw [heig Bs hBs (Φ ρ) w v hv]
  congr 1
  unfold M.xC cpol
  rw [show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rho_eq]
  have h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ) := by
    have := hL j.succ
    simp only [Fin.val_succ] at this
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [shf, Φ, hβ]
  push_cast
  rw [← h]
  ring

end Formalism.FourierDecayAlt.P.ProductIntervalFrames

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by
  intro hK Wp _ _ _ P hOK hu'
  obtain ⟨k, r, T, T', u, u'⟩ := P
  dsimp only at hu'
  subst hu'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩
  intro z e π hz hT hπ he hez hee
  exact ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee

end Formalism.FourierDecayAlt.P
end
end

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.FrameExtension

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frame_weaken {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) : IsFrameOf k r [z] Bs := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, fun a v hv => h3 a v (by rw [List.mem_singleton] at hv; subst hv; simp)⟩

private theorem hpk_apply_comm (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

private theorem star_hpk_apply (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp

private theorem herm_hpk_eq_star_herm_swap (k r : ℕ) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, star_hpk_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_apply_comm]
  ring

theorem frame_snoc {k r m : ℕ} {z e : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (h : IsFrameOf k r [z, e] Bs) (he : inWb k r e) (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) :
    IsFrameOf k r [z] (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => ?_, fun a b => ?_, fun a v hv => ?_⟩
  · induction a using Fin.lastCases with
    | last => simpa using he
    | cast i => simpa using h1 i
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => simpa using hee
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last j).ne', herm_hpk_eq_star_herm_swap, h3 j e (by simp), star_zero]
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        rw [if_neg (Fin.castSucc_lt_last i).ne, h3 i e (by simp)]
      | cast j =>
        simp only [Fin.snoc_castSucc]
        rw [h2 i j]
        simp [Fin.castSucc_inj]
  · rw [List.mem_singleton] at hv
    subst hv
    induction a using Fin.lastCases with
    | last => simpa using hez
    | cast i => simpa using h3 i v (by simp)

theorem subA_EB {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r m : ℕ} (π : Mx k r → (W →L[ℂ] W))
    (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (e : Fin (2 * r + k + 1) → ℂ) :
    subA (EB π (Fin.snoc (α := fun _ => Fin (2 * r + k + 1) → ℂ) Bs e)) = EB π Bs := by
  funext a b
  simp [subA, EB, unitB, Fin.snoc_castSucc]

theorem prod_Icc_fin (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Finset.Icc 1 (n + 1), f i = ∏ j : Fin (n + 1), f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n + 1)]
    simp

end Formalism.FourierDecayAlt.P.FrameExtension

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qr_branchingK_of : Qr.BranchingAlg → Qr.FrameGl → Qr.LieStab → Qr.StabLie → Qr.FrameChange →
    Qr.FrameExists2 → Qr.BranchingK := by
  intro hBA hFG hLS hSL hFC hFE Wp _ _ _ n r z e π u β L hz hT hty hL hu he hez hee
  obtain ⟨hnt, hrep, hcont, -, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨Bs₀, hB₀⟩ := hFE n r z e hz hT he hez hee
  have hB₁ := FrameExtension.frame_snoc hB₀ he hez hee
  set Bs₁ : Fin (n + 1) → Fin (2 * r + (n + 1) + 1) → ℂ :=
    Fin.snoc (α := fun _ => Fin (2 * r + (n + 1) + 1) → ℂ) Bs₀ e with hBs₁
  have hsub : subA (EB π Bs₁) = EB π Bs₀ := FrameExtension.subA_EB π Bs₀ e
  obtain ⟨hgl, hq⟩ := hFG Wp (n + 1) r (n + 1) z π Bs₁ hR hB₁
  have hH : Hyp (EB π Bs₁) β L := by
    refine ⟨hgl, ⟨hnt, fun S hS => hirr S (hLS Wp (n + 1) r z π Bs₁ hz hT hR hB₁ S hS)⟩, hL, ?_⟩
    intro w v
    rw [← hq w v, hcap Bs₁ hB₁ w v, FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [← hu j]
    ring
  obtain ⟨hint, hS⟩ := hBA Wp n (EB π Bs₁) β L hH
  rw [hsub] at hint hS
  refine ⟨fun M => CapSp (EB π Bs₀) (shf β M.1), hint, fun M => ⟨(hS M).1, fun S' hle hst => ?_⟩, ?_⟩
  · exact (hS M).2 S' hle (hSL Wp (n + 1) r n z e π Bs₀ hR hB₀ S' hst)
  · intro Bs hBs M w v hv
    rw [(hFG Wp (n + 1) r n z π Bs hR (FrameExtension.frame_weaken hBs)).2 w v,
      hFC Wp n r z e π Bs Bs₀ hz hT he hez hee hR hBs hB₀ w]
    exact Qr.mem_CapSp.1 hv w

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def regE (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r D.z D.z' g}

theorem regE_sub (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : regE D ε ⊆ B.GV k r := fun _ hg => hg.1

theorem scal_bound_of_ubl (D : B.RealPlaceData k r Wp Wq) (φ : B.Mat k r → ℂ) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (regE D ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem dlast_pos (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {g : B.Mat k r} (hg : ε ≤ Gf k r D.z D.z' g) :
    ε ≤ Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) :=
  Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg

theorem dlast_ne (D : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ B.GPos D) :
    Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
  intro h
  have := dlast_pos D hg.2 (le_refl _)
  rw [h, map_zero] at this
  linarith [hg.2]

theorem open_dlast (z z' : Fin (2 * r + k + 1) → ℂ) :
    IsOpen {g : B.Mat k r | Dmin k r z z' g (Fin.last (r + 1)) ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' _).continuous continuous_const

theorem ckOn_phiR (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiR k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiR k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h0 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' ⟨r, by omega⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  refine (h0.contDiffOn.mul (h1.contDiffOn.inv (fun x hx => hx))).congr (fun x _ => ?_)
  simp [phiR, div_eq_mul_inv]

theorem ckOn_phiD (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiD k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiD k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => (starRingEnd ℂ) (Dmin k r D.z D.z' g (Fin.last (r + 1)))) :=
    Complex.conjCLE.contDiff.comp h1
  refine (h1.contDiffOn.mul (h2.contDiffOn.inv (fun x hx => by simpa using hx))).congr (fun x _ => ?_)
  simp [phiD, div_eq_mul_inv]

theorem phiR_le (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiR k r D.z D.z' g‖ ≤ C0 := by
  set T := Tz k r D.z * Tz k r D.z' with hT
  have hT0 : 0 < T := mul_pos D.T_pos D.T'_pos
  refine ⟨1 + 1 / T, fun g hg => ?_⟩
  have hG := hg.2
  have h1 := dlast_pos D hε hG
  have hpos : 0 < Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) := lt_of_lt_of_le hε h1
  unfold Gf at hG
  set a := Complex.normSq (Dmin k r D.z D.z' g ⟨r, by omega⟩)
  set b := Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1)))
  have hsq : ‖phiR k r D.z D.z' g‖ ^ 2 = a / b := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [phiR, Complex.normSq_div]
    rfl
  have hle : a / b ≤ 1 / T := by
    rw [div_le_div_iff₀ hpos hT0]
    nlinarith
  nlinarith [sq_nonneg (‖phiR k r D.z D.z' g‖ - 1)]

theorem phiD_le (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiD k r D.z D.z' g‖ ≤ C0 := by
  refine ⟨1, fun g _ => ?_⟩
  simp only [phiD, norm_div, Complex.norm_conj]
  exact div_self_le_one _

theorem ubl_phiR (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiR k r D.z D.z') (regE D ε) n r (r + 1) := by
  have hP0 : U.IsPolyDeg r (fun g : B.Mat k r => Dmin k r D.z D.z' g ⟨r, by omega⟩) :=
    Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' ⟨r, by omega⟩
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have ha := ubl_poly hP0 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP1 (regE_sub D ε) hε (fun g hg => dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiR k r D.z D.z' = fun g => Dmin k r D.z D.z' g ⟨r, by omega⟩ *
      (Dmin k r D.z D.z' g (Fin.last (r + 1)))⁻¹ ^ 1 := by
    funext g; simp [phiR, div_eq_mul_inv]
  rw [e]
  simpa using hm

theorem ubl_phiD (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiD k r D.z D.z') (regE D ε) n (r + 1) (r + 1) := by
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have hP2 := Formalism.FourierDecayAlt.P.CutMP.jdh_pd_star hP1
  have ha := ubl_poly hP1 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP2 (regE_sub D ε) hε
    (fun g hg => by simpa [Complex.star_def] using dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiD k r D.z D.z' = fun g => Dmin k r D.z D.z' g (Fin.last (r + 1)) *
      (star (Dmin k r D.z D.z' g (Fin.last (r + 1))))⁻¹ ^ 1 := by
    funext g; simp [phiD, div_eq_mul_inv]
  rw [e]
  simpa using hm

end

theorem scalar_transfer_bound_holds : JAScalBound := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ D Bg hBg
  refine ⟨⟨ckOn_phiR D, fun ε hε m => ?_⟩, ⟨ckOn_phiD D, fun ε hε m => ?_⟩⟩
  · exact scal_bound_of_ubl D _ r (r + 1) Bg (by push_cast; linarith) ε (phiR_le D hε)
      (fun n => ubl_phiR D hε n) m
  · exact scal_bound_of_ubl D _ (r + 1) (r + 1) Bg (by push_cast; linarith) ε (phiD_le D ε)
      (fun n => ubl_phiD D hε n) m

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
