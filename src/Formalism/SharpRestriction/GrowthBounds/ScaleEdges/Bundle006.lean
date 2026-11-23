module

public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EDelApply
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RemainingWeightVectorCount
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SymbolRealisableBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

theorem num_E (c' r k Q N₁ : ℕ) (hk : k ≤ c') (hN : N₁ ≤ k) (hN1 : 1 ≤ N₁) (hr : 2 ≤ r) (hQ : 3 ≤ Q) :
    (c' * (1 + r * k * Q) + c') * Q + (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤
      15 * c' * (N₁ + r * k) * Q ^ 2 := by
  have h1 : (2 * Q + 3) * c' + k * Q ≤ 4 * Q * c' := by
    nlinarith [Nat.mul_le_mul_right Q hk, Nat.mul_le_mul_right c' hQ]
  have h2 : N₁ + 1 ≤ 2 * k := by omega
  have h3 : (N₁ + 1) * (((2 * Q + 3) * c' + k * Q) * (r * Q)) ≤ (2 * k) * ((4 * Q * c') * (r * Q)) :=
    Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h1)
  have h5 : 2 ≤ r * k * Q := by
    calc 2 = 2 * 1 * 1 := by norm_num
      _ ≤ r * k * Q := Nat.mul_le_mul (Nat.mul_le_mul hr (by omega)) (by omega)
  have h4 : (c' * (1 + r * k * Q) + c') * Q ≤ 2 * (c' * (r * k) * Q ^ 2) := by
    have e : (c' * (1 + r * k * Q) + c') * Q = c' * Q * 2 + c' * Q * (r * k * Q) := by ring
    have e2 : 2 * (c' * (r * k) * Q ^ 2) = c' * Q * (r * k * Q) + c' * Q * (r * k * Q) := by ring
    rw [e, e2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h5) _
  have e3 : (2 * k) * ((4 * Q * c') * (r * Q)) = 8 * (c' * (r * k) * Q ^ 2) := by ring
  have e4 : 15 * c' * (N₁ + r * k) * Q ^ 2 = 15 * (c' * N₁ * Q ^ 2) + 15 * (c' * (r * k) * Q ^ 2) := by ring
  rw [e3] at h3
  rw [e4]
  omega

theorem multidegree_bound_le_a (C k r N Q c' Y a N₁ : ℝ) (hC : 30 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hc : 0 ≤ c') (hY : 1 ≤ Y) (hN1 : N₁ ≤ k) (h : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y ≤ a) :
    15 * c' * (N₁ + r * k) * Q ^ 2 ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr2 : r ≤ r ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have hQ5 : Q ^ 2 ≤ Q ^ 5 := pow_le_pow_right₀ hQ (by norm_num)
  have hQ2 : 0 ≤ Q ^ 2 := by positivity
  have h1 : N₁ + r * k ≤ 2 * (r * k) := by nlinarith
  have h2 : 15 * c' * (N₁ + r * k) * Q ^ 2 ≤ 15 * c' * (2 * (r * k)) * Q ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) hQ2
  have a1 : 30 * k ≤ C * k ^ 3 := mul_le_mul hC hk3 (by linarith) (by linarith)
  have a2 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 := mul_le_mul a1 hr2 (by linarith) (by positivity)
  have a3 : 30 * k * r ≤ C * k ^ 3 * r ^ 2 * N := le_trans a2 (le_mul_of_one_le_right (by positivity) hN)
  have a4 : 30 * k * r * Q ^ 2 ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 := mul_le_mul a3 hQ5 hQ2 (by positivity)
  have a5 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' := mul_le_mul_of_nonneg_right a4 hc
  have a6 : 30 * k * r * Q ^ 2 * c' ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * c' * Y :=
    le_trans a5 (le_mul_of_one_le_right (by positivity) hY)
  have e : 15 * c' * (2 * (r * k)) * Q ^ 2 = 30 * k * r * Q ^ 2 * c' := by ring
  linarith

theorem spdeg {C : ℝ} (hC : 30 ≤ C) {p n' m r : ℕ} [Fact p.Prime] [NeZero n'] {TT : Finset (Fin n')} {L₁ L₂ : ℕ}
    {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar)
    {F : Frames n' r} (hF : FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F) (t : Fin n') (ht : t ∈ F.TT) :
    eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
        E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
      eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤ flatDeg lam0 t := by
  have hB := hyps_basic (C := C) (by linarith) H
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := H
  have hTT := hF.1
  have hGn : goodG' r de h x ≤ n' := by have := h3.2.2.2; omega
  have hI : Formalism.G0.CondIntervals n' (F.TT.map Fin.valEmbedding) (goodG' r de h x) (orbitWindowCount r de h x) := by
    rw [hTT]
    exact h3.1.2.2
  have hG1 : 1 ≤ goodG' r de h x := le_trans hB.one_le_depth_alt hB.depth_le_good_exponent
  have hpR : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h1
  have hkR : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h2
  have hNR : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hQR : (p : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := le_self_pow₀ (by linarith) (by omega)
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := by linarith
  have hcR : (8 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (8 : ℝ) ≤ (cStar : ℝ) := by
      have : 8 ≤ cStar := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  have sq_level_le_degree : orbitWindowCount r de h x ≤ m + 1 := by omega
  have hE0a : ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) ≤ a := by
    have := multidegree_bound_le_a C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x)
      ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y a (orbitWindowCount r de h x : ℝ) hC hkR hrR hNR hQ1
      (by linarith) (by linarith [hB.two_le_Y]) (by exact_mod_cast sq_level_le_degree) h12
    refine le_trans (le_of_eq ?_) this
    unfold E0 cPrime
    push_cast
    ring

  have hpa : (p : ℝ) ≤ a := by
    have hE : (p : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) *
        ((orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ)) * ((p : ℝ) ^ goodG' r de h x) ^ 2 := by
      have b1 : (1 : ℝ) ≤ 15 * ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) := by linarith
      have b2 : (1 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) + r * ((m + 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ (orbitWindowCount r de h x : ℝ) := Nat.cast_nonneg _
        nlinarith
      have b3 : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 2 := le_trans hQR (le_self_pow₀ hQ1 (by norm_num))
      have b4 := one_le_mul_of_one_le_of_one_le b1 b2
      calc (p : ℝ) = 1 * p := by ring
        _ ≤ _ := mul_le_mul b4 b3 (by linarith) (by linarith)
    refine le_trans hE (le_trans (le_of_eq ?_) hE0a)
    unfold E0 cPrime
    push_cast
    ring
  have hlog : 1 ≤ Real.logb p a := by
    rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_one]
    exact hpa
  have hkD : ((m + 1 : ℕ) : ℝ) ≤ Dp := by
    refine le_trans ?_ h10
    have c1 : (1 : ℝ) ≤ C * (TT.card : ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hNR
    have c2 : ((m + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := le_self_pow₀ hkR (by norm_num)
    have c3 : ((m + 1 : ℕ) : ℝ) ≤ C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 := by
      calc ((m + 1 : ℕ) : ℝ) = 1 * ((m + 1 : ℕ) : ℝ) := by ring
        _ ≤ _ := mul_le_mul c1 c2 (by linarith) (by linarith)
    exact le_trans c3 (le_mul_of_one_le_right (by positivity) hlog)
  have hkc : m + 1 ≤ cPrime n' r TT.card c0 cpp cStar := by
    have : m + 1 ≤ Dp := by exact_mod_cast hkD
    unfold cPrime
    omega
  have hQ3 : 3 ≤ p ^ goodG' r de h x := by
    calc 3 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ goodG' r de h x := Nat.pow_le_pow_right (by omega) hG1
  have hle := eSP_le (p := p) hF (by omega) hGn hI (m + 1) (cPrime n' r TT.card c0 cpp cStar) t
  have hnum := num_E (cPrime n' r TT.card c0 cpp cStar) r (m + 1) (p ^ goodG' r de h x) (orbitWindowCount r de h x) hkc sq_level_le_degree
    (one_le_orbitWindowCount r de h x) h2 hQ3
  have hfin : eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t ≤
      E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) := by
    unfold E0
    exact le_trans hle hnum
  refine ⟨hfin, ?_⟩
  have hfd := (flatDeg_bounds (by have := hB.m_ge; omega) (by linarith [hB.two_le_a]) h5 t (hTT ▸ ht)).1
  have : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
      (flatDeg lam0 t : ℝ) := by
    have h0 : ((eSP p n' F (m + 1) (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) t : ℕ) : ℝ) ≤
        ((E0 p r (m + 1) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) : ℕ) : ℝ) := by
      exact_mod_cast hfin
    linarith
  exact_mod_cast this

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def CloudAtX (p n' : ℕ) [Fact p.Prime] [NeZero n'] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [Algebra (WF p n') O]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) {m r : ℕ}
    (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (cStar : ℕ) (bS bT bD : ℝ)
    (e : Edge W Qq (m + 1)) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) : Prop :=
  ∃ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
    IsFlatIdent ι σ w φ r (dT TT lam0) (flW (dT TT lam0)) (vecE n') h Θ ∧
    ∃ (n2 oS tT D1 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)),
      (oS : ℝ) ≤ bS ∧ (tT : ℝ) ≤ bT ∧ (D1 : ℝ) ≤ bD ∧
      (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e ∧
        sh i ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (HL (O := O) ι σ (restW TT lam0) e.src)) ∧
      ((n2 : ℕ) : ℚ) = remainingWeightVectorCount TT lam0 ∧
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O, (∃ x, IsUnit (c x)) →
          ∃ G : Module.Dual Kf (Vsp Kf lam0),
            G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
            G ∈ Re' p ι σ w r lam0 e ∧
            (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
              G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
            ValLe (p : O) D1 (be p r lam0 (∑ x, c x • S x) G)

def CloudStepX (C Ct0 CD1 CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      CloudAtX p n' ι σ w φ (r := r) TT lam0 cStar (om r TT.card n' c0 cpp)
        (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp)
        (CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e hm FsB

def RestCloudX (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudStepX C Ct0 CD1 CLa

theorem restCloud_of_X (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hX : RestCloudX D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RestCloud D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨Ct0, CD1, C₁, h0, h1, h2, hS⟩ := hX hA h14a h14b
  have h35 : tableLineDegreeFive.FewBadOrbits D := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨Ct0, CD1, max C₁ 2, h0, h1, lt_of_lt_of_le h2 (le_max_left _ _), ?_⟩
  intro C hC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  obtain ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4, a5, a6⟩ :=
    hS C (le_trans (le_max_left _ _) hC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H
      φ hφ K hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB
  exact ⟨Θ, hΘ, n2, oS, tT, D1, sh, a1, a2, a3, a4,
    count_of_exact D h35 (le_trans (le_max_right _ _) hC) H Kf n2 a5, a6⟩

end Formalism.MainNotions.Pf14
end
end
