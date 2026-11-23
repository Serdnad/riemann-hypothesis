module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
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

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def RestSExp (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)),
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      ThZ B K' vp (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestSInt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' r0 r1 : ℕ) (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U))

def RestSExpA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (j : ℕ) (Ph : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)),
    Simeq p Ph (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

def RestSIntA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ (j : ℕ) (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)))

section Formal

variable {p : ℕ} [hp : Fact p.Prime]

theorem sSer_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (sSer p K' e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : Zidx n' r0 r1 →₀ ℕ).degree + 1),
    if (0 : Zidx n' r0 r1 →₀ ℕ) = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhS_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p K' u) = 0 := by
  unfold hhS

  simp only [map_sum, map_mul, sSer_const, mul_zero, Finset.sum_const_zero]

theorem coordZ_const {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>

  simp only [coordZ, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZ_mul {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (f g : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') :
    ThZ B K' vp (f * g) = ThZ B K' vp f * ThZ B K' vp g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZ_const B K' vp)) f g

theorem map_map_tower {ι : Type} (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) f) =
      MvPowerSeries.map (algebraMap (K0 p) K') f := by
  rw [IsScalarTower.algebraMap_eq (K0 p) K1 K', MvPowerSeries.map_comp]
  rfl

theorem atPi_mul {σ R : Type} [CommRing R] (vp : R) (f g : MvPowerSeries σ R) :
    atPi vp (f * g) = atPi vp f * atPi vp g := by
  classical
  ext n
  show vp ^ n.degree * MvPowerSeries.coeff n (f * g) = MvPowerSeries.coeff n (atPi vp f * atPi vp g)
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  show _ = (vp ^ x.1.degree * MvPowerSeries.coeff x.1 f) * (vp ^ x.2.degree * MvPowerSeries.coeff x.2 g)
  rw [← hx', map_add (f := _), pow_add]
  ring

theorem exp_change {ι : Type} (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : K') (hh hh' G : MvPowerSeries ι K')
    (h0 : MvPowerSeries.constantCoeff hh = 0) (h0' : MvPowerSeries.constantCoeff hh' = 0)
    (hE : hh' = hh + MvPowerSeries.C (p : K') * G) :
    expK (-(MvPowerSeries.C (c / (p : K')) * hh)) =
      expK (-(MvPowerSeries.C (c / (p : K')) * hh')) * expK (MvPowerSeries.C c * G) := by
  have := charZero_K' p K'
  have hp0 := pK'_ne p K'
  have hG : MvPowerSeries.constantCoeff G = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hE
    rw [map_add (f := _), map_mul, h0, h0', zero_add, MvPowerSeries.constantCoeff_C] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hp0
    · exact h
  rw [← expK_add (by rw [map_neg, map_mul, h0', mul_zero, neg_zero]) (by rw [map_mul, hG, mul_zero])]
  congr 1
  have e : (MvPowerSeries.C (c / (p : K')) : MvPowerSeries ι K') * MvPowerSeries.C (p : K') = MvPowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp0]
  rw [hE, mul_add, ← mul_assoc, e]
  ring

end Formal

theorem SConcl_of {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (hD : DworkLemma p) (hE : RestSExp p) (hI : RestSInt p)
    {n' r0 r1 : ℕ} (h2 : 2 ≤ n') (hev : Even n') (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1)
    (hK : ExtensionLocalCondition p K1 R1 be Th) : SConcl B K1 R1 Th := by
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hK
  intro K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨u, hu, V, hV, hEq⟩ := hE h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' vp hvp
  refine ⟨u, fun s => hRp (hu s), fun hh' h0' hG => ?_⟩
  obtain ⟨G, hG, hhE⟩ := hG
  have hW := hI n' r0 r1 B K1 R1 U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hh')) *
        (expK (MvPowerSeries.C (vp ^ (p + 1)) * G) * V * ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U)) := by
    rw [hTh, map_mul, map_map_tower, ThZ_mul, hEq,
      exp_change K' (vp ^ (p + 1)) (hhS p K' u) hh' G (hhS_const K' u) h0' hhE]
    ring
  rw [e1]
  exact inClass_of_exp (pK'_ne p K') hc hh' h0' (IntR_mul (IntR_mul (IntR_expK hc hG) (IntR_mono hRp hV)) hW)

theorem kernel_expansion_of_restrictions (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExp p) (hI : RestSInt p) : Conclusion1 D X Y := by
  intro v j hj La La' h1 h2 φ
  exact SConcl_of (X.std v).five_le (hA.1 p) hE hI (X.std v).two_le (X.std v).even (X.om v) Y.Kc Y.Oc Y.be _
    (hA.2.1 v j hj La La' h1 h2 φ)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_m_ge (hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : 2 ≤ (D.gat u w hg).P.m := by
  have h1 := hT.gat_k u w hg
  have h2 := D.R.m_add_three_le_k
  omega

theorem nc_cG_nonneg : 0 ≤ Formalism.MainNotions.G.cG L := by
  unfold Formalism.MainNotions.G.cG
  have h := L.Sc_pos
  linarith

private theorem liftWt_apply_of_lt_succ (t m : ℕ) (lam : Fin (m + 1) → ℤ) (w : ℕ → ℤ) (j i : ℕ)
    (hi : i < m + j * (t + 1) + 1) (h : i < m + 1) :
    Formalism.MainNotions.G.liftWt t m lam w j ⟨i, hi⟩ = lam ⟨i, h⟩ :=
  dif_pos h

private theorem lam_antitone_of_isDominant_liftWt {n' m : ℕ} (t : ℕ) (lam : Fin n' → Fin (m + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (hd : Formalism.MainNotions.G.IsDominant fun s => Formalism.MainNotions.G.liftWt t m (lam s) (fun i => w i s) 0)
    (s : Fin n') (i i' : ℕ) (hi : i < m + 1) (hi' : i' < m + 1) (hii : i ≤ i') :
    lam s ⟨i', hi'⟩ ≤ lam s ⟨i, hi⟩ := by
  unfold Formalism.MainNotions.G.IsDominant at hd
  have h1 := hd s (show (⟨i, by omega⟩ : Fin (m + 0 * (t + 1) + 1)) ≤ ⟨i', by omega⟩ from
    Fin.mk_le_mk.mpr hii)
  calc lam s ⟨i', hi'⟩ = Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i', by omega⟩ :=
        (liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i' (by omega) hi').symm
    _ ≤ Formalism.MainNotions.G.liftWt t m (lam s) (fun j => w j s) 0 ⟨i, by omega⟩ := h1
    _ = lam s ⟨i, hi⟩ := liftWt_apply_of_lt_succ t m (lam s) (fun j => w j s) 0 i (by omega) hi

private theorem lamI_one_eq_lam0_zero {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 = lam0 s ⟨0, by omega⟩ :=
  dif_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem lamI_two_eq_lam0_one {n' k1 : ℕ} (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (s : Fin n')
    (hk : 1 ≤ k1) : Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 = lam0 s ⟨1, by omega⟩ :=
  dif_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem nu_one_eq_lamI_one_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 1 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 1 + w j s :=
  if_pos (show 1 ≤ 1 ∧ 1 ≤ k1 + 1 from ⟨le_refl 1, by omega⟩)

private theorem nu_two_eq_lamI_two_add_w {n' k1 : ℕ} (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ)
    (w : ℕ → Fin n' → ℤ) (j : ℕ) (s : Fin n') (hk : 1 ≤ k1) :
    Formalism.MainNotions.FormalGroupSystem.nu t lam0 w j s 2 = Formalism.MainNotions.FormalGroupSystem.lamI lam0 s 2 + w j s :=
  if_pos (show 1 ≤ 2 ∧ 2 ≤ k1 + 1 from ⟨by omega, by omega⟩)

private theorem le_of_monotone_from_one (f : ℕ → ℤ) (h : ∀ j, 1 ≤ j → f j ≤ f (j + 1)) :
    ∀ j, 1 ≤ j → f 1 ≤ f j := by
  intro j hj
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    · have hn0 : n = 0 := by omega
      subst hn0
      exact le_refl _
    · exact (ih hn).trans (h n hn)

private theorem le_and_neg_le_of_abs_le_of_le (x : ℤ) (c : ℕ) (g : ℝ) (hx : |x| ≤ (c : ℤ)) (hc : (c : ℝ) ≤ g) :
    (x : ℝ) ≤ g ∧ -(x : ℝ) ≤ g := by
  have h := abs_le.mp hx
  have h1 : (x : ℝ) ≤ (c : ℝ) := by exact_mod_cast h.2
  have h2 : -(c : ℝ) ≤ (x : ℝ) := by exact_mod_cast h.1
  constructor <;> linarith

theorem nc_ties (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    let v := Y.vOf u w hg t0
    let Fl := Y.Fl u w hg
    (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
    (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
    (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) := by
  dsimp only
  unfold Formalism.MainNotions.G.LatTied at hL
  have hm : 2 ≤ (D.gat u w hg).P.m := nc_m_ge hT u w hg
  have hm1 : 1 ≤ (D.gat u w hg).P.m := by omega
  have hcG : (0 : ℝ) ≤ Formalism.MainNotions.G.cG L := nc_cG_nonneg
  obtain ⟨-, -, hc, -, -, -, hrep⟩ := hL u w hg
  obtain ⟨-, hs⟩ := hrep t0 ht0
  have hbase := (Y.Fl u w hg).base (Y.vOf u w hg t0)
  unfold Formalism.MainNotions.G.IsBaseWeight at hbase
  have hd := (Y.Fl u w hg).domJ 0 (Y.vOf u w hg t0)
  have hwge := (Y.Fl u w hg).w_ge (Y.vOf u w hg t0)
  have hwm := (Y.Fl u w hg).w_mono (Y.vOf u w hg t0)
  have h0 : 0 < (D.gat u w hg).P.m + 1 := by omega
  have h1 : 1 < (D.gat u w hg).P.m + 1 := by omega
  have hM : (D.gat u w hg).P.m < (D.gat u w hg).P.m + 1 := by omega
  have e0 : (0 : Fin ((D.gat u w hg).P.m + 1)) = ⟨0, h0⟩ := Fin.ext (by simp)
  have hA01 : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 0 1 h0 h1 (by omega)
  have hA1M : ∀ s, (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩ := fun s =>
    lam_antitone_of_isDominant_liftWt (Y.Fl u w hg).t ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
      ((Y.Fl u w hg).w (Y.vOf u w hg t0)) hd s 1 (D.gat u w hg).P.m h1 hM (by omega)
  have hTT1 : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨1, h1⟩| ≤ ((Y.Fl u w hg).c : ℤ) :=
    fun s hsT => ((hbase s).1 hsT).2.2 ⟨1, h1⟩ Nat.one_pos (show 1 < (D.gat u w hg).P.m by omega)
  have hA : ∀ s, s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      (D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩ = (Y.Fl u w hg).a (Y.vOf u w hg t0) s := by
    intro s hsT
    rw [← e0]
    exact ((hbase s).1 hsT).1
  have hN0 : ∀ s, s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0) →
      |(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨0, h0⟩| ≤ ((Y.Fl u w hg).c : ℤ) := by
    intro s hsT
    rw [← e0]
    exact (hbase s).2 hsT 0
  have hwZ : ∀ s, -(D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s ⟨(D.gat u w hg).P.m, hM⟩ ≤
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s := fun s => (le_max_right _ _).trans (hwge s)
  have hwj : ∀ s j, 1 ≤ j →
      (Y.Fl u w hg).w (Y.vOf u w hg t0) 1 s ≤ (Y.Fl u w hg).w (Y.vOf u w hg t0) j s :=
    fun s => le_of_monotone_from_one (fun j => (Y.Fl u w hg).w (Y.vOf u w hg t0) j s) (fun j hj => hwm s j hj)
  have hj1 : 1 ≤ j := by
    unfold Formalism.BasicNotions.SizeData₂.lifts at hj
    exact (Finset.mem_Icc.mp hj).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hsT
    have hA' := (hA s hsT).trans ((hs s).2.2.1 hsT).1
    have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_ya Formalism.MainNotions.G.al Formalism.MainNotions.FormalGroupSystem.al
    simp only [hsT, ↓reduceIte]
    rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1, hA']
    push_cast
    linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.al
    split_ifs with hsT
    · rw [lamI_one_eq_lam0_zero, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA01 s]
    · exact le_refl 0
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.Pf.nc_zc Formalism.MainNotions.FormalGroupSystem.cap
    rw [← (hs s).2.2.2 j hj]
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hTT1 s hsT) hc).1
      push_cast
      linarith
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      have hB := (le_and_neg_le_of_abs_le_of_le _ _ _ (hN0 s hsT) hc).1
      push_cast
      linarith
  · intro s
    unfold Formalism.MainNotions.FormalGroupSystem.cap
    split_ifs with hsT
    · rw [nu_two_eq_lamI_two_add_w _ _ _ _ _ hm1, lamI_two_eq_lam0_one _ _ hm1]
      linarith [hA1M s, hwZ s, hwj s j hj1]
    · rw [nu_one_eq_lamI_one_add_w, lamI_one_eq_lam0_zero]
      linarith [hA01 s, hA1M s, hwZ s, hwj s j hj1]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
