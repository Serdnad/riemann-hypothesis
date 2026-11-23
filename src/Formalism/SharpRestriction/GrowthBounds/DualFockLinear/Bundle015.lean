module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle014
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.FlipOneThree
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.Interval.Finset.Box
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

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14

theorem num_size2 (C k r N Q cS c0 z Y a : ℝ) (hC : 2 ≤ C) (hk : 1 ≤ k) (hr : 2 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 8 ≤ cS) (hc0 : 0 ≤ c0) (hz : 0 ≤ z) (hY : 2 ≤ Y)
    (hsz : C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y ≤ a) : 8 * k ≤ a := by
  have hk3 : k ≤ k ^ 3 := le_self_pow₀ hk (by norm_num)
  have hr2 : 4 ≤ r ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hr 2
    norm_num at h
    linarith
  have hQ5 : 1 ≤ Q ^ 5 := one_le_pow₀ hQ
  have hW : 8 ≤ cS + (r * N * c0 + z) := by
    have : 0 ≤ r * N * c0 := by positivity
    linarith
  have hchain : 2 * k * 4 * 1 * 1 * 8 * 2 ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + (r * N * c0 + z)) * Y := by
    gcongr
  linarith

theorem log_size_bound_le (p n' m : ℕ) (TT : Finset (Fin n')) (X : Fin n' → Fin (m + 1) → ℤ) (a : ℝ) (hp : 1 < p) (ha : 1 ≤ a)
    (h0 : ∀ s, s ∉ TT → ellWt (lamAt X s) = 0)
    (h1 : ∀ s ∈ TT, ((ellWt (lamAt X s) : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ a ^ 2) :
    ((kap1 p X : ℕ) : ℝ) ≤ 2 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.logb p a := Real.logb_nonneg hp' ha
  unfold kap1
  rw [Nat.cast_sum]
  have hterm : ∀ s, (((if ellWt (lamAt X s) = 0 then 0 else N0 (m + 1) * deF p (m + 1) (ellWt (lamAt X s)) : ℕ)) : ℝ) ≤
      if s ∈ TT then 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a else 0 := by
    intro s
    by_cases hs : s ∈ TT
    · rw [if_pos hs]
      split_ifs with hz
      · rw [Nat.cast_zero]
        exact mul_nonneg (by positivity) hlog
      · rw [Nat.cast_mul]
        have hN0 : ((N0 (m + 1) : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
          have : N0 (m + 1) ≤ (m + 1) ^ 2 := by
            unfold N0
            calc (m + 1) * (m + 1 - 1) / 2 ≤ (m + 1) * (m + 1 - 1) := Nat.div_le_self _ _
              _ ≤ (m + 1) * (m + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
              _ = (m + 1) ^ 2 := by ring
          exact_mod_cast this
        have hde : ((deF p (m + 1) (ellWt (lamAt X s)) : ℕ) : ℝ) ≤ 2 * Real.logb p a := by
          unfold deF
          have hpos : (0 : ℝ) < ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) := by
            have : 0 < ellWt (lamAt X s) + (m + 1) - 1 := by omega
            exact_mod_cast this
          have hle : ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) ≤ a ^ 2 := by
            have h2 : ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) ≤ ((ellWt (lamAt X s) + (m + 1) : ℕ) : ℝ) := by
              exact_mod_cast Nat.sub_le _ _
            have h3 := h1 s hs
            rw [Nat.cast_add] at h2
            linarith
          calc ((Nat.log p (ellWt (lamAt X s) + (m + 1) - 1) : ℕ) : ℝ)
              ≤ Real.logb p ((ellWt (lamAt X s) + (m + 1) - 1 : ℕ) : ℝ) := Real.natLog_le_logb _ _
            _ ≤ Real.logb p (a ^ 2) := Real.logb_le_logb_of_le hp' hpos hle
            _ = 2 * Real.logb p a := by rw [Real.logb_pow]; norm_num
        calc ((N0 (m + 1) : ℕ) : ℝ) * ((deF p (m + 1) (ellWt (lamAt X s)) : ℕ) : ℝ)
            ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (2 * Real.logb p a) := mul_le_mul hN0 hde (Nat.cast_nonneg _) (by positivity)
          _ = 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a := by ring
    · rw [if_neg hs, if_pos (h0 s hs), Nat.cast_zero]
  calc _ ≤ ∑ s : Fin n', (if s ∈ TT then 2 * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a else 0) :=
        Finset.sum_le_sum fun s _ => hterm s
    _ = _ := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        ring

theorem lastIdx_eq (m : ℕ) : lastIdx (m + 1) = Fin.last m :=
  Fin.ext (by simp [lastIdx])

theorem ellWt_zero (m : ℕ) : ellWt (0 : Fin (m + 1) → ℤ) = 0 := by
  simp [ellWt]

theorem ellWt_flat {n' m : ℕ} (hm : 1 ≤ m) (d : Fin n' → ℕ) (s : Fin n') : ellWt (lamAt (flW (m := m) d) s) = d s := by
  have hne : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  simp only [lamAt, flW, ellWt, lastIdx_eq]
  split_ifs
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne hne, sub_zero]
    simp
  · simp only [Fin.rev_zero, Fin.rev_last, Pi.single_eq_same, Pi.single_eq_of_ne hne, neg_zero,
      zero_sub, neg_neg]
    simp

theorem sizeStep (C : ℝ) (hC : 2 ≤ C) : SizeStep C 4 := by
  intro p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar H
  have hkc := rank_mul_conductor_div_le_one hC H
  obtain ⟨hp, hr, _, hN1, hW, hY, _, hk, _, hD, hc, hsz⟩ := H
  have hm2 : 2 ≤ m := by omega
  have hN1pos : 1 ≤ orbitWindowCount r de h x := by unfold orbitWindowCount; omega
  have hNnat : 1 ≤ TT.card := by
    rcases Nat.eq_zero_or_pos TT.card with h0' | h0'
    · rw [h0', Nat.mul_zero] at hN1
      have : 0 < orbitWindowCount r de h x ^ 2 := by positivity
      omega
    · exact h0'
  have hN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hNnat
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ m + 1 := by omega
    exact_mod_cast this
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp1 : (1 : ℝ) < p := by
    have : 1 < p := by omega
    exact_mod_cast this
  have hQ : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1.le
  have hY2 : (2 : ℝ) ≤ Y := le_trans hr2 hY
  have hc0 : (0 : ℝ) ≤ c0 := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ 2 * (r : ℝ) * n' * cpp := by positivity
  have hcS : (8 : ℝ) ≤ cStar := by
    have : 8 ≤ cStar := by omega
    exact_mod_cast this
  have h8 := num_size2 C _ _ _ _ _ _ _ Y a hC hk1 hr2 hN hQ hcS hc0 hz hY2 hsz
  have ha8 : 8 ≤ a := by linarith
  have hapos : 0 < a := by linarith
  have hkc' : ((m + 1 : ℕ) : ℝ) * c0 ≤ a := by rwa [div_le_one hapos] at hkc
  have hc0a : (c0 : ℝ) ≤ a := le_trans (le_mul_of_one_le_left hc0 hk1) hkc'
  have hsq : 4 * a ≤ a ^ 2 := by nlinarith
  have A := log_size_bound_le p n' m TT (topW TT lam0) a (by omega) (by linarith)
    (fun s hs => by rw [lamAt_zero (by simp [topW, hs])]; exact ellWt_zero m)
    (fun s hs => by
      rw [lamAt_congr (show topW TT lam0 s = lam0 s by simp [topW, hs])]
      obtain ⟨hb, hdom, hw⟩ := hW
      obtain ⟨e0, elast, _⟩ := (hb s).1 hs
      obtain ⟨w1, w2, hb0, hbc⟩ := hw s hs
      have hzz : lamAt lam0 s 0 - lamAt lam0 s (Fin.last m) = aT s + bT s := by
        unfold lamAt
        split_ifs
        · rw [e0, elast]; ring
        · simp only [Fin.rev_zero, Fin.rev_last]
          rw [e0, elast]; ring
      have haT : 0 ≤ aT s := by
        have : (0 : ℝ) ≤ (aT s : ℝ) := by
          have : (0 : ℝ) ≤ cpp := Nat.cast_nonneg _
          linarith
        exact_mod_cast this
      have e1 : ((ellWt (lamAt lam0 s) : ℕ) : ℝ) = ((aT s + bT s : ℤ) : ℝ) := by
        unfold ellWt
        rw [lastIdx_eq, hzz, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      have hbT : (bT s : ℝ) ≤ c0 := by
        have : bT s ≤ c0 := by omega
        exact_mod_cast this
      have hcp : (0 : ℝ) ≤ cpp := Nat.cast_nonneg _
      rw [e1]
      push_cast
      push_cast at h8
      linarith)
  have B := log_size_bound_le p n' m TT (flW (m := m) (dT TT lam0)) a (by omega) (by linarith)
    (fun s hs => by rw [ellWt_flat (by omega)]; simp [dT, hs])
    (fun s hs => by
      rw [ellWt_flat (by omega)]
      have := (flatDeg_bounds hm2 hapos.le hW s hs).2
      simp only [dT, if_pos hs]
      push_cast
      push_cast at h8
      linarith)
  rw [Nat.cast_add]
  linarith

theorem restSize : RestSize := ⟨4, 2, by norm_num, by norm_num, fun C hC => sizeStep C hC⟩

theorem restCloudB_of_op (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_two D CLa Ck Crk Cdeg hop restSize

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData

def NSAt (CH CE C6 C18 : ℝ) (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (w : O) {m : ℕ} (r : ℕ)
    (TT : Finset (Fin n')) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1)
    (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (c0 cP κ : ℕ) (bD : ℝ) {nb : ℕ} (B : Fin nb → RRing O n' (r + K)) : Prop :=
  ∃ DX : ℕ, (DX : ℝ) ≤ bD ∧
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => symP p O hk hrk Fr cP (p ^ G') (B b))) →
      HasMultideg G d → InWj w G 0 → ¬ InWj w G 1 →
      ∃ (J : ℕ) (_ : NeZero J) (Dt : SignedChainData p O r J) (F2 : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)),
        Dt.Hyp CH ∧ 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c ∧ Dt.XX F2 ∧ vBB (O := O) p F2 = 0 ∧
        ∀ Gp R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O),
          (∀ mo, geQ (vK p (Gp.coeff mo)) 0) → Dt.YY C6 C18 Gp →
          (∀ mo, geQ (vK p (R.coeff mo)) (Dt.c - Dt.EE CE)) →
          (∀ mo ∈ Gp.support ∪ R.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) →
          geQ (vBB (O := O) p (Dt.ph (Gp + R))) (Dt.n0 - Dt.kp) →
          leQ (vK p (Dt.Bform F2 (Dt.ph (Gp + R)))) (Dt.EE CE + 2 * Dt.kp + Dt.n0 - Dt.kp) →
          ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
            (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
            ValLe (Kf := KK O) (p : O) DX
              ((p : KK O) ^ κ * fock G (∑ q, sig q) / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O))

theorem xiAtP_of_NS {CH CE C6 C18 : ℝ} {p : ℕ} {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {w : O} {m : ℕ} {r : ℕ}
    {TT : Finset (Fin n')} {d deg : Fin n' → ℕ} {K : ℕ} [NeZero r] [NeZero K] {hk : m + 1 = r + K} {hrk : r ≤ m + 1}
    {Fr : Frames n' r} {N₁ G' : ℕ} {Y : ℝ} {c0 cP κ : ℕ} {bD : ℝ} {nb : ℕ} {B : Fin nb → RRing O n' (r + K)}
    (h14b : ProjectionDerivativeEstimate p O CH CE C6 C18)
    (hN : NSAt CH CE C6 C18 p w r TT d deg K hk hrk Fr N₁ G' Y c0 cP κ bD B) :
    XiAtP p w r TT d deg K hk hrk Fr N₁ G' Y c0 cP κ bD B := by
  obtain ⟨DX, hDX, hN⟩ := hN
  refine ⟨DX, hDX, fun G h1 h2 h3 h4 => ?_⟩
  obtain ⟨J, hJ, Dt, F2, a1, a2, a3, a4, a5⟩ := hN G h1 h2 h3 h4
  obtain ⟨Gp, R, b1, b2, b3, b4, b5, b6⟩ := h14b r J Dt a1 a2 F2 a3 a4
  exact a5 Gp R b1 b2 b3 b4 b5 b6

def NSStep (C CD CLa CH CE C6 C18 : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
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
        NSAt CH CE C6 C18 p w r TT (dT TT lam0) (flatDeg lam0) K hk hrk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0
          (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0))
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) B

def RestNS (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → NSStep C CDf CLa CH CE C6 C18

theorem restXiP_of_NS (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestNS D CLa Ck Crk Cdeg CH CE C6 C18) : RestXiP D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA h14b
  obtain ⟨CDf, C₁, h1, h2, h3⟩ := hN hA
  refine ⟨CDf, C₁, h1, h2, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K
    _ _ hk hrk F hF E' hE' nb B hB hli hc
  have hG1 : AdmissibleDVR p n' O := Formalism.MainNotions.flipOneThree.admissible_dvr_of_unramified_quadratic_setting hSet
  have hK : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero (dvrOfStd hSet) hG1.prime
  have hO : CharZero O := (algebraMap O (KK O)).charZero
  exact xiAtP_of_NS (h14b p O ⟨⟨dvrOfStd hSet⟩, n', hG1⟩)
    (h3 C hC p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk hrk F hF E' hE' nb B hB
      hli hc)

theorem restXi_of_NS (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hN : RestNS D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  restXi_of_P D CLa Ck Crk Cdeg CH CE C6 C18 (restXiP_of_NS D CLa Ck Crk Cdeg CH CE C6 C18 hN)

end Formalism.MainNotions.TestSideCounting
end
end
