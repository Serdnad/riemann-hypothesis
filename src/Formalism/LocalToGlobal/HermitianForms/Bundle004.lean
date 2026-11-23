module

public import Formalism.LocalToGlobal.HermitianForms.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.L2.Forms
open Formalism.BasicNotions

def uN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.k then h.u ⟨j, hj⟩ else 0
def vN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.k - 1 then h.v ⟨j, hj⟩ else 0
def bN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.m then h.b ⟨j, hj⟩ else 0
def eN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.m then h.e ⟨j, hj⟩ else 0

theorem uN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.k) : h.u ⟨j, hj⟩ = uN h j := by simp [uN, hj]
theorem vN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.k - 1) : h.v ⟨j, hj⟩ = vN h j := by simp [vN, hj]
theorem bN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.m) : h.b ⟨j, hj⟩ = bN h j := by simp [bN, hj]
theorem eN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.m) : h.e ⟨j, hj⟩ = eN h j := by simp [eN, hj]

def lamQ (R : Ranks) (h : HCParam R) (n : ℕ) : ℚ :=
  if n < R.k then uN h n - (((R.k : ℚ) - 1) / 2 - n)
  else -wG R (eN h ((n - R.k) / (R.t + 1))) ((n - R.k) / (R.t + 1) + 1)

def sgQ (R : Ranks) (h : HCParam R) (n : ℕ) : ℚ :=
  ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2 +
  (if n < R.k - 1 then vN h n
   else if (n - (R.k - 1)) % (R.t + 1) = 0 then -bN h ((n - (R.k - 1)) / (R.t + 1))
     else -eN h ((n - (R.k - 1)) / (R.t + 1)) + ((R.t : ℚ) - 1) / 2 - ((((n - (R.k - 1)) % (R.t + 1) : ℕ) : ℚ) - 1))
  - (((R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 2) / 2 - n)

theorem half_gap (a b : ℚ) (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (hab : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨z', rfl⟩ := hb
  have : z' ≤ z := by
    by_contra hc
    have h1 : z + 1 ≤ z' := by omega
    have h2 : ((z : ℚ) + 1) ≤ z' := by exact_mod_cast h1
    linarith
  have h2 : (z' : ℚ) ≤ z := by exact_mod_cast this
  linarith

theorem half_gap' (a b : ℚ) (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (hab : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨z', rfl⟩ := hb
  have : z + 1 ≤ z' := by
    by_contra hc
    have h1 : z' ≤ z := by omega
    have h2 : (z' : ℚ) ≤ z := by exact_mod_cast h1
    linarith
  have h2 : ((z : ℚ) + 1) ≤ z' := by exact_mod_cast this
  linarith

theorem interlaceQ (R : Ranks) (h : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    sgQ R h n ≤ lamQ R h n ∧ lamQ R h (n + 1) ≤ sgQ R h n := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · have hnk : n < R.k := by omega
    have hnk1 : n + 1 < R.k := by omega
    have g1 := half_gap _ _ (h.u_half ⟨n, hnk⟩) (h.v_int ⟨n, h1⟩) (h.u_gt_v ⟨n, h1⟩)
    have g2 := half_gap' _ _ (h.u_half ⟨n + 1, hnk1⟩) (h.v_int ⟨n, h1⟩) (h.v_gt_u ⟨n, h1⟩)
    rw [uN_eq, vN_eq] at g1 g2
    simp only [sgQ, lamQ, if_pos h1, if_pos hnk, if_pos hnk1]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha⟩ : ∃ a, n = R.k - 1 + a := ⟨n - (R.k - 1), by omega⟩
    have ha' : n - (R.k - 1) = a := by omega
    have hq : a / (R.t + 1) < R.m := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]; omega
    have hdm := Nat.div_add_mod a (R.t + 1)
    have hr := Nat.mod_lt a (Nat.succ_pos R.t)
    set q := a / (R.t + 1) with hqd
    set ρ := a % (R.t + 1) with hρd
    have hnQ : (n : ℚ) = (R.k : ℚ) - 1 + ((R.t : ℚ) + 1) * q + ρ := by
      have : n + 1 = R.k + ((R.t + 1) * q + ρ) := by omega
      have h2 : ((n + 1 : ℕ) : ℚ) = ((R.k + ((R.t + 1) * q + ρ) : ℕ) : ℚ) := by rw [this]
      push_cast at h2; linarith
    have hn1 : ¬ (n + 1 < R.k) := by omega
    have hi1 : (n + 1 - R.k) / (R.t + 1) = q := by
      have : n + 1 - R.k = a := by omega
      rw [this]
    have gbe := h.gap_be ⟨q, hq⟩
    rw [eN_eq, bN_eq] at gbe
    simp only [sgQ, lamQ, if_neg h1, if_neg hn1, ha', hi1, wG, ← hqd, ← hρd]
    by_cases hρ : ρ = 0
    · simp only [if_pos hρ]
      rw [hρ] at hnQ
      by_cases hq0 : q = 0
      · have hnk : n < R.k := by
          have : a = 0 := by rw [← hdm, hρ, hq0]; simp
          omega
        have hnk' : n = R.k - 1 := by omega
        have g0 := h.u_last_gt (by omega) (by omega)
        have g1 := half_gap _ _ (h.u_half ⟨R.k - 1, by omega⟩) (by
          obtain ⟨z, hz⟩ := h.b_int ⟨0, by omega⟩
          exact ⟨-z, by rw [hz]; push_cast; ring⟩) g0
        rw [uN_eq, bN_eq] at g1
        simp only [if_pos hnk]
        rw [hq0] at hnQ gbe ⊢
        rw [hnk']
        rw [hnk'] at hnQ
        push_cast at hnQ ⊢
        constructor <;> linarith
      · have hnk : ¬ n < R.k := by
          have : 0 < q := Nat.pos_of_ne_zero hq0
          have : R.t + 1 ≤ (R.t + 1) * q := Nat.le_mul_of_pos_right _ this
          omega
        obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := Nat.exists_eq_succ_of_ne_zero hq0
        have hi0 : (n - R.k) / (R.t + 1) = q' := by
          have : n - R.k = (R.t + 1) * q' + R.t := by
            have h3 : a = (R.t + 1) * (q' + 1) := by rw [← hdm, hρ, hq']; simp
            rw [Nat.mul_add] at h3
            omega
          rw [this, Nat.mul_add_div (Nat.succ_pos _)]
          rw [Nat.div_eq_of_lt (Nat.lt_succ_self _)]; simp
        have geb := h.gap_eb ⟨q', by omega⟩ (by show q' + 1 < R.m; omega)
        rw [eN_eq] at geb
        have geb' : ((R.t : ℚ) + 3) / 2 ≤ bN h (q' + 1) - eN h q' := by
          rw [← bN_eq h (q' + 1) (by omega)]; exact geb
        simp only [if_neg hnk, hi0]
        rw [hq'] at hnQ gbe ⊢
        push_cast at hnQ ⊢
        constructor <;> nlinarith
    · simp only [if_neg hρ]
      have hnk : ¬ n < R.k := by omega
      have hi0 : (n - R.k) / (R.t + 1) = q := by
        obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ = ρ' + 1 := Nat.exists_eq_succ_of_ne_zero hρ
        have : n - R.k = (R.t + 1) * q + ρ' := by omega
        rw [this, Nat.mul_add_div (Nat.succ_pos _)]
        rw [Nat.div_eq_of_lt (by omega)]; simp
      simp only [if_neg hnk, hi0]
      push_cast
      constructor <;> nlinarith

theorem sg_interlace {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) :
    (D.fm u).SgInterlace := by
  intro τ i
  have hi := i.2
  have key := interlaceQ D.R (D.hcW u τ) i.1 hi
  have hN : (((D.R.N D.R.m - 1 : ℕ)) : ℚ) = (D.R.k : ℚ) + (D.R.m : ℚ) * ((D.R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (D.R.N_pos D.R.m)]; unfold Ranks.N; push_cast; ring
  have hs : (((D.fm u).sg τ).w i : ℚ) = sgQ D.R (D.hcW u τ) i.1 := by
    rw [W.sg τ i]
    unfold sgHC sgQ rhoVec
    rw [hN]
    by_cases h1 : i.1 < D.R.k - 1
    · simp only [dif_pos h1, if_pos h1, vN_eq]; ring
    · have h2 : (i.1 - (D.R.k - 1)) / (D.R.t + 1) < D.R.m := by
        apply Nat.div_lt_of_lt_mul
        have := D.R.m_add_three_le_k
        unfold Ranks.N at hi
        rw [Nat.mul_comm]; omega
      simp only [dif_neg h1, dif_pos h2, if_neg h1, bN_eq, eN_eq]; ring
  have hl : ∀ n (hn : n < D.R.N D.R.m), (((D.fm u).lam D.R.m τ).w ⟨n, hn⟩ : ℚ) = lamQ D.R (D.hcW u τ) n := by
    intro n hn
    rw [(D.fm u).lam_eq D.R.m le_rfl τ ⟨n, hn⟩]
    unfold lamQ
    by_cases h : n < D.R.k
    · simp only [dif_pos h, if_pos h, hcToWeightQ, rhoVec, uN_eq]
    · simp only [dif_neg h, if_neg h, eN_eq]
  constructor
  · have := key.1
    rw [← hs, ← hl i.1 (by omega)] at this
    exact_mod_cast this
  · have := key.2
    rw [← hs, ← hl (i.1 + 1) (by omega)] at this
    exact_mod_cast this

end Formalism.L2.Forms
end

section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Matrix

theorem isUnit_det_cols {E : Type} [Field E] {N n : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hA : Function.Injective A.mulVec) (hz : ∀ x, A *ᵥ x ≠ z) :
    IsUnit (Matrix.of (fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a)).det := by
  subst hN
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v1 v2 h12
  have hv : (Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ (v1 - v2) = 0 := by
    rw [Matrix.mulVec_sub, h12, sub_self]
  rw [← sub_eq_zero]
  generalize v1 - v2 = v at hv ⊢
  have hsplit : ∀ a, ((Matrix.of fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) *ᵥ v) a =
      (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a := by
    intro a
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, mul_comm]
  have hv' : ∀ a, (A *ᵥ fun j => v j.castSucc) a + v (Fin.last n) * z a = 0 := fun a => by
    rw [← hsplit]; exact congrFun hv a
  have hlast : v (Fin.last n) = 0 := by
    by_contra h
    apply hz (-(v (Fin.last n))⁻¹ • fun j : Fin n => v j.castSucc)
    funext a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    have e : (A *ᵥ fun j : Fin n => v j.castSucc) a = -(v (Fin.last n) * z a) := by linear_combination hv' a
    rw [e]; field_simp
  have hcs : (fun j : Fin n => v j.castSucc) = 0 := by
    apply hA
    funext a
    have := hv' a
    rw [hlast, zero_mul, add_zero] at this
    rw [this, Matrix.mulVec_zero]; rfl
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · exact hlast
  · exact congrFun hcs i

variable (D : D7)

theorem iX'_injective : letI := D.host.cmStar; Function.Injective D.sp.iX' := by
  letI := D.host.cmStar
  intro x y h
  rw [← sub_eq_zero]
  have h0 : D.sp.iX' (x - y) = 0 := by rw [map_sub, h, sub_self]
  apply D.sp.X'.nondeg.1 (x - y)
  intro w
  rw [← D.sp.iX'_isom (x - y) w, h0, map_zero, LinearMap.zero_apply]

theorem iXc_injective : Function.Injective (iXc D) := by
  letI := D.host.cmStar
  intro x y h
  unfold iXc at h
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, EmbeddingLike.apply_eq_iff_eq] at h
  exact (LinearEquiv.injective _) (iX'_injective D h)

theorem iXm_mulVec_injective : Function.Injective (iXm D).mulVec := by
  intro x y h
  simp only [iXm, LinearMap.toMatrix'_mulVec] at h
  exact iXc_injective D h

variable {D}

end Formalism.L2.Forms
end
end

section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

def EvzTie {u : D.what₂.Word} {A : AtTTied u} {K : ClsPTied u} {P : LvTied u A D.R.m le_rfl}
    {Tl : TilTied u A K P} {Km : ClsTied u D.R.m le_rfl}
    (Ta : TilAd Tl Km) (W : ValTied u A.eV D.R.m le_rfl Km)
    (eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)) : Prop :=
  ∀ (φ : (D.mem u).C.cls D.R.m → (D.mem u).C.Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) (Tl.ga c).1.1) (W.eY s') (W.eY s) →
    eWz ((D.mem u).P.evz φ) c s = (((Km.lev.chi (Ta.ka c))⁻¹ : ℂˣ) : ℂ) * φ ((D.fm u).til c) s'


open Classical in
def BwTie {u : D.what₂.Word} (A : AtTTied u) {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u A.eV i hi K) : Prop :=
  ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (D.fm u).seenP w = true →
    ∀ v (x : ((D.fm u).lat i).V), x ∈ (D.fm u).Bw i w v ↔
    ∀ (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i x c z =
        fnOf _ (shiftOf (lamT u i))
          (fun τ => if τ = (D.fm u).tauOf w v then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ
            else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1 τ) P (W.eY z)

def PerTie (u : D.what₂.Word) (jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow) : Prop :=
  (∀ z ∈ (D.fm u).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (D.fm u).ptC) ∧
    ∀ w F, (D.mem u).P.period w F = (D.fm u).ipP (jM F) w

def subP {ι : Type} {n : ℕ} (o : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  MvPolynomial.aeval fun x => ∑ a', MvPolynomial.C (o x.1 x.2.1 a') * MvPolynomial.X (x.1, a', x.2.2)

def embS (D : D7) (s : D.what₂.LL →+* ℂ) : D.what₂.Tau → D.host.E →+* ℂ :=
  fun τ => s.comp (D.embE.comp (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

def NormTie {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {i : ℕ} {hi : i ≤ D.R.m} {K : ClsTied u i hi}
    (W : ValTied u eV i hi K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : ((D.fm u).lat i).V)
    (Pc : (D.mem u).C.cls i → MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) D.what₂.LL),
    (∀ c z, (D.fm u).emb i x c z =
      fnOf _ (shiftOf (lamT u i)) 1 (MvPolynomial.map D.what₂.embLL (Pc c)) (W.eY z)) →
    ∀ o : Frames (gramC (gramN D i hi) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat i).b ((D.fm u).lat i).X (InfinitePlace.mk s) x x).re =
        ∑ c, ((D.mem u).C.wt i c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u i) τ)) *
          (nfAll ((D.fm u).lam i) (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def NormPTie {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : (D.fm u).ptLat.V)
    (Pc : (D.fm u).clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW ((D.fm u).ptEmb x) c =
      fnOf _ (shiftOf (sgT u)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgT u) τ)) *
          (nfAll (D.fm u).sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

def aOf (R : Ranks) (i : ℕ) : ℕ := if i < R.m then R.k + i else R.r

def skipOf (R : Ranks) (i : ℕ) : ℕ := if i + 1 < R.m then R.k else R.N i

def fcOf (R : Ranks) (i : ℕ) : ℕ := if R.m ≤ i + 1 then R.k else R.N i

theorem fcOf_lt {R : Ranks} {i : ℕ} (h : i + 1 < R.m) : fcOf R i = R.N i := if_neg (Nat.not_le.2 h)



structure FormsTied (D : D7) (u : D.what₂.Word) where
  atT : AtTTied u
  cls : ∀ i hi, ClsTied u i hi
  val : ∀ i hi, ValTied u atT.eV i hi (cls i hi)

  gl : GLoc D.host.F D.host.E (sigD D) D.host.g
  gl_K : ∀ i, (gl.piG i : D.host.E) ∈ D.host.K

  glev : ∀ i hi, GLev (cls i hi).lev gl (aOf D.R i) D.R.t i (skipOf D.R i) (fcOf D.R i) (decide (i = D.R.m))
  lv : ∀ i hi, LvTied u atT i hi
  fMe : ∀ i hi v, (cls i hi).lev.fM (atT.eV v).1 (atT.eV v).2 ≃+ (D.mem u).A.Fv v
  fv : ∀ i hi, FvTie (lv i hi) (cls i hi) (fMe i hi)

  upN : ∀ i hi, UpNatTie (lv i hi) (cls i hi) (val i hi)
  dnN : ∀ i hi, DnNatTie (lv i hi) (cls i hi) (val i hi)
  norm : ∀ i hi, NormTie (val i hi)
  bw : ∀ i hi, BwTie atT (val i hi)
  clsP : ClsPTied u
  valP : ValPTied u clsP
  normP : NormPTie valP

  glevP : GLev clsP.lev gl D.R.r D.R.t D.R.m (D.R.N D.R.m) (fcOf D.R D.R.m) false
  til : TilTied u atT clsP (lv D.R.m le_rfl)
  tilLat : TilBaseLat til (cls D.R.m le_rfl)
  tilFv : TilBaseFv til (cls D.R.m le_rfl) (fMe D.R.m le_rfl)
  tilAd : TilAd til (cls D.R.m le_rfl)
  frExt : FrExt til.z0 (glev D.R.m le_rfl) glevP
  eWz : (D.mem u).P.Wz ≃ₗ[ℂ] ((D.fm u).clsP → (D.mem u).C.Y D.R.m → ℂ)
  evz : EvzTie tilAd (val D.R.m le_rfl) eWz
  jM : (D.mem u).P.Mt →ₛₗ[starRingEnd ℂ] (D.mem u).P.Wrow
  per : PerTie u jM

  DGam : (D.mem u).C.DGam = (D.mem D.u₀).C.DGam

theorem Mu0_iff {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :
    φ ∈ (D.mem u).A.Mu0 ↔
      (fun c z => φ c (W.eY.symm z)) ∈ FiC K.lev (embT D) ((D.fm u).lam 0) K.y := by
  rw [← (D.fm u).Fi_zero, ← lamT_zero]; exact W.Fi φ

theorem rhoT_eq {u : D.what₂.Word} {eV : (D.mem u).A.vT ≃ PlT D u} {K : ClsTied u 0 (Nat.zero_le _)}
    (W : ValTied u eV 0 (Nat.zero_le _) K) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ)
    (hk : (k : (D.mem u).A.Fv v) = a) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia K.lev (eV v).1 (eV v).2 k δ) (g) (hg : g ∈ AdFun K.lev (embT D)) :
    (D.mem u).A.rhoT v a (fun c s => g (K.y c) (W.eY s)) = fun c s => g (K.y c * δ) (W.eY s) := by
  funext c
  rw [(D.fm u).rhoT_dil]
  exact W.dilT v a k hk c δ hδ g hg

end Formalism.L2.Forms
end
end
