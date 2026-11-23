module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle003
public import Formalism.PolynomialDimension.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NumBase
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FourDepthLtConductorOfBounds
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsRingChange
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HarProjEqZeroIff
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility Formalism.CountingSumsFrames MvPolynomial

def RS.Ov {p n' : ℕ} (R : RS p n') : ValuationSubring R.Kf :=
  { (algebraMap R.O R.Kf).range with
    mem_or_inv_mem' := by
      intro x
      have := R.std.1.frac_O
      rcases ValuationRing.isInteger_or_isInteger R.O x with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact Or.inl ⟨a, ha⟩
      · exact Or.inr ⟨a, ha⟩ }

theorem RS.mem_Ov {p n' : ℕ} (R : RS p n') (a : R.O) : algebraMap R.O R.Kf a ∈ R.Ov.toSubring := ⟨a, rfl⟩

theorem RS.pLocal {p n' : ℕ} (R : RS p n') : PLocal R.Ov.toSubring p := by
  intro n hn
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    have := (Nat.Prime.coprime_iff_not_dvd R.std.1.prime).2 hn
    exact (Nat.isCoprime_iff_coprime.2 this).symm
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit (n : R.O) := by
    by_contra hnu
    have h1 : (n : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have h2 : (p : R.O) ∈ IsLocalRing.maximalIdeal R.O := (IsLocalRing.mem_maximalIdeal _).2 R.p_not_unit
    have h3 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) ∈ IsLocalRing.maximalIdeal R.O :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    have h4 : ((a : R.O) * (n : R.O) + (b : R.O) * (p : R.O)) = 1 := by
      have := congrArg (fun z : ℤ => (z : R.O)) hab
      simpa using this
    rw [h4] at h3
    exact (IsLocalRing.mem_maximalIdeal _).1 h3 isUnit_one
  obtain ⟨v, hv⟩ := hu
  refine ⟨((v⁻¹ : R.Oˣ) : R.O), ?_⟩
  have h5 : algebraMap R.O R.Kf ((v⁻¹ : R.Oˣ) : R.O) * (n : R.Kf) = 1 := by
    rw [← map_natCast (algebraMap R.O R.Kf) n, ← hv, ← map_mul, Units.inv_mul, map_one]
  exact eq_inv_of_mul_eq_one_left h5

def TwoLetterModelIdentification : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m →
    ∃ (α : ∀ P Q : ℕ, twoSp R.Kf m P Q ≃ₗ[R.Kf] PolAB R.Kf (m + 1) P Q)
      (β : ∀ a b : ℕ, PolAB R.Kf (m + 1) a b →ₗ[R.Kf] dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m a b))),
      (∀ a b, Function.Surjective (β a b)) ∧
      (∀ a b (f : PolAB R.Kf (m + 1) a b), β a b f = 0 ↔
        ∃ G ∈ PolAB R.Kf (m + 1) (a - 1) (b - 1), (f : PolXY R.Kf (m + 1)) = hXY R.Kf (m + 1) * G) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∃ g' : GL (Fin (m + 1)) R.Kf,
        (∀ (P Q : ℕ) (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf), x ∈ twoLat R.O m P Q Λ ↔
          ∃ hx : x ∈ twoSp R.Kf m P Q,
            (α P Q ⟨x, hx⟩ : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring)) ∧
        (∀ (a b : ℕ) (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf), y ∈ H0 R.O m (wtPQ m a b) Λ ↔
          ∃ f : PolAB R.Kf (m + 1) a b, (f : PolXY R.Kf (m + 1)) ∈ latOf g' (GaussLat R.Ov.toSubring) ∧
            (β a b f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = y)

theorem expo_le (p a m P Q : ℕ) (hp : 2 ≤ p) (h : P + Q + 1 ≤ 8 * a) :
    (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) ≤ ⌈((m : ℝ) + 2) * lgA p a m⌉₊ := by
  have h1 : (Nat.log p (P + Q + (m + 1)) : ℝ) ≤ Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have h2 : Real.logb p ((P + Q + (m + 1) : ℕ) : ℝ) ≤ Real.logb p (8 * (a : ℝ) + m) := by
    apply Real.logb_le_logb_of_le hp1
    · have : 0 < P + Q + (m + 1) := by omega
      exact_mod_cast this
    · have : P + Q + (m + 1) ≤ 8 * a + m := by omega
      exact_mod_cast this
  have h3 : (((m + 1 + 1) * Nat.log p (P + Q + (m + 1)) : ℕ) : ℝ) ≤ ((m : ℝ) + 2) * lgA p a m := by
    unfold lgA
    push_cast
    have hm : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
    have : ((m : ℝ) + 1 + 1) = (m : ℝ) + 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hm
  exact_mod_cast le_trans h3 (Nat.le_ceil _)

theorem single_weight_of_model_identification (h : TwoLetterModelIdentification) : SingleWeightLatticeComparison := by
  classical
  intro p n' R m hm a P Q hPQ
  obtain ⟨α, β, hsurj, hker, hlat⟩ := h p n' R m hm
  have : CharZero R.Kf := R.charZero
  have hp := R.std.1.prime
  obtain ⟨io, pr, hsum, hL⟩ := oneTop_abs R.Kf (m + 1) P Q p (by omega) hp R.Ov R.pLocal (α P Q)
    (fun j => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) (fun j => β (P - j) (Q - j))
    (fun j => hsurj _ _) (fun j f => hker _ _ f)
  set E := (m + 1 + 1) * Nat.log p (P + Q + (m + 1)) with hE
  set U := ⌈((m : ℝ) + 2) * lgA p a m⌉₊ with hU
  have hEU : E ≤ U := expo_le p a m P Q hp.two_le hPQ
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hEU
  have hpd : (p : R.Kf) ^ d ∈ R.Ov.toSubring := Subring.pow_mem _ (natCast_mem _ p) d
  have hexI : ∀ j, ∃ I : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
      MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf,
      I ∘ₗ (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype =
        (twoSp R.Kf m P Q).subtype ∘ₗ io j := fun j => LinearMap.exists_extend _
  have hexP : ∀ j, ∃ Pj : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
      MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf,
      Pj ∘ₗ (twoSp R.Kf m P Q).subtype =
        (dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))).subtype ∘ₗ pr j :=
    fun j => LinearMap.exists_extend _
  choose I hI using hexI
  choose Pj hPj using hexP
  have hI' : ∀ j (y : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))),
      I j (y : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) = (io j y : MvPolynomial _ R.Kf) :=
    fun j y => LinearMap.congr_fun (hI j) y
  have hP' : ∀ j (x : twoSp R.Kf m P Q),
      Pj j (x : MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf) = (pr j x : MvPolynomial _ R.Kf) :=
    fun j x => LinearMap.congr_fun (hPj j) x
  refine ⟨I, Pj, ?_, ?_, ?_⟩
  · intro x hx
    have h0 := congrArg (twoSp R.Kf m P Q).subtype (hsum ⟨x, hx⟩)

    rw [map_sum] at h0
    calc ∑ j ∈ Finset.range (min P Q + 1), I j (Pj j x)
        = ∑ j ∈ Finset.range (min P Q + 1), (twoSp R.Kf m P Q).subtype (io j (pr j ⟨x, hx⟩)) :=
          Finset.sum_congr rfl fun j _ => by rw [hP' j ⟨x, hx⟩, hI']; rfl
      _ = x := h0
  · intro j _
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · rw [hP' j ⟨x, hx⟩]; exact (pr j ⟨x, hx⟩).2
    · rw [hI' j ⟨y, hy⟩]; exact (io j ⟨y, hy⟩).2
  · intro Λ hΛ j hj
    obtain ⟨g', h1, h2⟩ := hlat Λ hΛ
    obtain ⟨hA, hB⟩ := hL g' j hj
    constructor
    · intro x hx
      obtain ⟨hx2, hx3⟩ := (h1 P Q x).1 hx
      obtain ⟨f, hf, hfe⟩ := hA ⟨x, hx2⟩ hx3
      refine (h2 (P - j) (Q - j) _).2 ⟨((p : R.Kf) ^ d) • f, smul_mem_latOf _ g' hpd hf, ?_⟩
      rw [map_smul, hfe, hP' j ⟨x, hx2⟩, Submodule.coe_smul, Submodule.coe_smul, smul_smul, hd, pow_add, mul_comm]
    · intro y hy
      obtain ⟨f, hf, hfe⟩ := (h2 (P - j) (Q - j) y).1 hy
      have h3 := hB f hf
      have hy2 : y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))) := by
        rw [← hfe]; exact (β (P - j) (Q - j) f).2
      have hyf : (⟨y, hy2⟩ : dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) = β (P - j) (Q - j) f :=
        Subtype.ext hfe.symm
      refine (h1 P Q _).2 ⟨?_, ?_⟩
      · rw [hI' j ⟨y, hy2⟩]
        exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2
      · have e : (⟨((p : R.Kf) ^ U) • I j y, by
            rw [hI' j ⟨y, hy2⟩]; exact Submodule.smul_mem _ _ (io j ⟨y, hy2⟩).2⟩ : twoSp R.Kf m P Q) =
            ((p : R.Kf) ^ d) • (((p : R.Kf) ^ E) • io j (β (P - j) (Q - j) f)) := by
          have hIy : I j y = (io j (β (P - j) (Q - j) f) : MvPolynomial _ R.Kf) := by
            rw [← hyf]; exact hI' j ⟨y, hy2⟩
          apply Subtype.ext
          show ((p : R.Kf) ^ U) • I j y = _
          rw [Submodule.coe_smul, Submodule.coe_smul, hIy, smul_smul, hd, pow_add, mul_comm]
        rw [e, map_smul, Submodule.coe_smul]
        exact smul_mem_latOf _ g' hpd h3

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem posAdd_cdist {n' : ℕ} (x y : Fin n') : posAdd x (cdist x y) = y := by
  apply Fin.ext
  show (x.val + (y.val + n' - x.val) % n') % n' = y.val
  rw [Nat.add_mod_mod]
  have h : x.val + (y.val + n' - x.val) = y.val + n' := by
    have := x.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]

theorem mem_segDists {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (d : ℕ) :
    d ∈ segDists TT j ↔ ∃ s ∈ TT, ¬ Even s.val ∧ 0 < cdist (segStart TT j) s ∧
      cdist (segStart TT j) s < segG TT j ∧ cdist (segStart TT j) s = d := by
  unfold segDists
  rw [Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩
  · rintro ⟨s, hs, h1, h2, h3, rfl⟩
    exact ⟨s, Finset.mem_filter.2 ⟨hs, h1, h2, h3⟩, rfl⟩

theorem segPos_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) (i : Fin (segS TT j)) :
    segPos TT j i ∈ TT ∧ ¬ Even (segPos TT j i).val ∧
      cdist (segStart TT j) (segPos TT j i) = (segDists TT j).get i ∧ 0 < (segDists TT j).get i ∧
      (segDists TT j).get i < segG TT j := by
  obtain ⟨s, hs, h1, h2, h3, h4⟩ := (mem_segDists TT j _).1 (List.get_mem (segDists TT j) i)
  have e : segPos TT j i = s := by
    unfold segPos
    rw [← h4]
    exact posAdd_cdist _ _
  rw [e]
  exact ⟨hs, h1, h4, h4 ▸ h2, h4 ▸ h3⟩

theorem mem_evenTops {n' : ℕ} (TT : Finset (Fin n')) (x : Fin n') : x ∈ evenTops TT ↔ x ∈ TT ∧ Even x.val := by
  unfold evenTops
  rw [Finset.mem_sort, Finset.mem_filter]

theorem segStart_spec {n' : ℕ} (TT : Finset (Fin n')) (j : Fin (numSeg TT)) :
    segStart TT j ∈ TT ∧ Even (segStart TT j).val :=
  (mem_evenTops TT _).1 (List.get_mem _ _)

theorem ex_cast {n' : ℕ} {TT : Finset (Fin n')} (z : Fin n' → ℤ) (c : ℕ) (s : Fin n') (hs : s ∈ TT) (h0 : 0 ≤ z s) :
    ((ex (TT := TT) (fun s => (z s + c).toNat) s : ℕ) : ℝ) = (z s : ℝ) + c := by
  unfold ex
  rw [dite_eq_left hs]
  have h : ((z s + c).toNat : ℤ) = z s + c := Int.toNat_of_nonneg (by positivity)
  have h' : (((z s + c).toNat : ℤ) : ℝ) = ((z s + c : ℤ) : ℝ) := by rw [h]
  push_cast at h'
  exact h'

theorem min_shift (b a c P : ℝ) (hc : 0 ≤ c) (hP : 1 ≤ P) : min (b + c) ((a + c) / P) ≤ min b (a / P) + c := by
  have hP0 : 0 < P := by linarith
  have h1 : c / P ≤ c := div_le_self hc hP
  have h2 : (a + c) / P = a / P + c / P := add_div _ _ _
  rw [← min_add_add_right]
  exact min_le_min le_rfl (by rw [h2]; linarith)

open Classical in
theorem tle_of (hO : RestOddTops) {K : Cst} (hK : K.Pos) {CH : ℝ} {C : ℝ} (hC : 4 * K.Ct + 4 ≤ C)
    {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) (aw bw : Fin X.n' → ℤ)
    (hw : ∀ s ∈ X.TT, aw s ∈ IaZ X.m X.Y X.ar ∧ bw s ∈ IbZ X.bl X.bu) :
    (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) + 2 * X.n' * X.ccl ≤
      tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw := by
  have hseg2 : 2 ≤ numSeg X.TT := h.2.2.2.1
  have hbl : 0 ≤ X.bl := by
    have := lowb_of h
    linarith [B.hb8]
  have hp1 : (1 : ℝ) ≤ X.p := by linarith [B.hp25]
  have har200 : (200 : ℝ) ≤ X.ar := by
    have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
    linarith [B.hpa]
  have ha0 : ∀ s ∈ X.TT, 0 ≤ aw s := fun s hs =>
    le_trans (Int.ceil_nonneg (by linarith)) (Finset.mem_Icc.1 (hw s hs).1).1
  have hb0 : ∀ s ∈ X.TT, 0 ≤ bw s := fun s hs =>
    le_trans (Int.ceil_nonneg hbl) (Finset.mem_Icc.1 (hw s hs).2).1
  set S : ℝ := ∑ y ∈ X.TT.filter (fun y => ¬ IsTypeV y),
      min (bw y : ℝ) ((aw (yPrev X.TT y) : ℝ) / (X.p : ℝ) ^ dPrev X.TT y) with hS
  set S' : ℝ := ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex (TT := X.TT) (fun s => (bw s + X.ccl).toNat) (segPos X.TT j i) : ℕ) : ℝ)
          (((ex (TT := X.TT) (fun s => (aw s + X.ccl).toNat) (segStart X.TT j) : ℕ) : ℝ) /
            (X.p : ℝ) ^ ((segDists X.TT j).get i)) with hS'
  have hcount : (∑ j : Fin (numSeg X.TT), ∑ _i : Fin (segS X.TT j), (X.ccl : ℝ)) ≤ X.N * X.ccl := by
    have := hO X.n' X.TT hseg2 (fun _ _ _ => (X.ccl : ℝ))
    rw [this, Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    unfold Dat.N
    exact_mod_cast Finset.card_filter_le _ _
  have hSS : S' ≤ S + X.N * X.ccl := by
    have e := hO X.n' X.TT hseg2 (fun y x d => min (bw y : ℝ) ((aw x : ℝ) / (X.p : ℝ) ^ d))
    have h1 : S' ≤ ∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        (min (bw (segPos X.TT j i) : ℝ) ((aw (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i)) +
          (X.ccl : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      rw [ex_cast bw X.ccl _ (segPos_spec X.TT j i).1 (hb0 _ (segPos_spec X.TT j i).1),
        ex_cast aw X.ccl _ (segStart_spec X.TT j).1 (ha0 _ (segStart_spec X.TT j).1)]
      exact min_shift _ _ _ _ (by positivity) (one_le_pow₀ hp1)
    simp only [Finset.sum_add_distrib] at h1
    rw [e] at h1
    linarith
  have hS'0 : 0 ≤ S' := by
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro i _
    exact le_min (by positivity) (by positivity)

  have ha1 : (1 : ℝ) ≤ X.a := by linarith [B.haa]
  have hlog0 : 0 ≤ Real.log X.a := Real.log_nonneg ha1
  have hlog2 : Real.log X.a ≤ 2 * Real.log X.ar := by
    have h10 : (X.a : ℝ) ≤ X.ar ^ 2 := by
      have : 2 * X.ar ≤ X.ar * X.ar := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have e : X.ar ^ 2 = X.ar * X.ar := by ring
      rw [e]
      linarith [B.haa1]
    have := Real.log_le_log (by linarith) h10
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by unfold LaI; exact mul_nonneg hcn hlog0
  have hLa'2 : LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar := by
    unfold LaI
    have := mul_le_mul_of_nonneg_left hlog2 hcn
    linarith
  have hk1 : (1 : ℝ) ≤ X.k := by linarith [B.hk5]
  have hb : 0 < X.b' := by linarith [B.hb8]
  have hp0 : (0 : ℝ) < X.p := by linarith
  have hJ : X.J0 K = LaI K.C₀ X.N₁ X.a * X.b' / X.k := rfl
  have key := tle_abs K.Ct C X.N X.N₁ X.p X.k ((X.p : ℝ) ^ X.G') (Real.logb X.p X.ar) X.ar X.a X.b'
    (LaI K.C₀ X.N₁ X.ar) (LaI K.C₀ X.N₁ X.a) X.ccl X.cStar X.n' S S' hK.2.2.2.2.2.2.2.1 hC (by linarith [B.hN2])
    B.hN1 hp0 hk1 B.hQ (by linarith [B.hL1]) (by linarith) (by linarith) (by linarith [B.haa1]) hb
    (by linarith [B.hLa1]) hLa'0 hLa'2 (by positivity) (by positivity) (by positivity) hSS
  have hx0 : 0 ≤ X.t0 K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) + X.N * X.J0 K := by
    rw [initial_level_formula, hJ]
    have hCt : 0 < K.Ct := hK.2.2.2.2.2.2.2.1
    have hk0 : 0 < X.k := by linarith
    have hQ0 : (0 : ℝ) < (X.p : ℝ) ^ X.G' := by positivity
    have := hS'0
    positivity
  have hceil : (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) ≤
      (S' + K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl))) +
        X.N * (LaI K.C₀ X.N₁ X.a * X.b' / X.k) + 1 := by
    have h1 := (Nat.ceil_lt_add_one hx0).le
    have h2 := initial_level_formula K X (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat)
    unfold Dat.tStar
    calc _ ≤ _ := h1
      _ = _ := by rw [h2, hJ]
  have htI : tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw =
      S + C * X.N * X.N₁ * (X.ar / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.ar * X.ar / (X.p * X.k) +
          LaI K.C₀ X.N₁ X.ar * X.b' / X.k) +
        C * X.N * ((X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + C * X.N * X.k * Real.logb X.p X.ar + 4 * X.N * X.ccl +
          2 * X.n' * X.ccl) + X.k * (X.p : ℝ) ^ X.G' + X.k * Real.logb X.p X.ar + X.ccl) + 2 * X.n' * X.ccl := rfl
  rw [htI]
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section

variable {p n' : ℕ} {R₁ R₂ : RS p n'} (I : RSIso R₁ R₂) {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem pm_symm (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) :
    I.symm.JO.pm (I.JO.pm P) = P := by
  show MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) (MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) P) = P
  have h : (I.φK.symm : R₂.Kf →+* R₁.Kf).comp (I.φK : R₁.Kf →+* R₂.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

theorem pm_symm' (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₂.Kf) :
    I.JO.pm (I.symm.JO.pm P) = P := by
  show MvPolynomial.map (I.φK : R₁.Kf →+* R₂.Kf) (MvPolynomial.map (I.φK.symm : R₂.Kf →+* R₁.Kf) P) = P
  have h : (I.φK : R₁.Kf →+* R₂.Kf).comp (I.φK.symm : R₂.Kf →+* R₁.Kf) = RingHom.id _ := by
    ext x; simp
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

def PsiV : Vsp R₁.Kf lam0 ≃+ Vsp R₂.Kf lam0 where
  toFun x := ⟨I.JO.pm x.1, Vsp_tr I lam0 x.1 x.2⟩
  invFun y := ⟨I.symm.JO.pm y.1, Vsp_tr I.symm lam0 y.1 y.2⟩
  left_inv x := Subtype.ext (pm_symm I x.1)
  right_inv y := Subtype.ext (pm_symm' I y.1)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem HLpoly_tr (L : Submodule R₁.W (Fin (m + 1) → R₁.Qq))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => extO R₁.O R₁.ι R₁.σ s.val L)) :
    I.JO.pm P ∈ Hten R₂.O lam0 (fun s => extO R₂.O R₂.ι R₂.σ s.val (mapSub I.JW L)) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => extO R₁.O R₁.ι R₁.σ s.val L) (P := P) hP
  simp only [extO_tr] at h
  exact h

theorem HLepoly_tr (e : Edge R₁.W R₁.Qq (m + 1))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf)
    (hP : P ∈ Hten R₁.O lam0 (fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e)) :
    I.JO.pm P ∈ Hten R₂.O lam0
      (fun s => LeAt p R₂.ι R₂.σ R₂.w s.val ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩) := by
  have h := Hten_tr (I := I) (lam0 := lam0) (Λ := fun s => LeAt p R₁.ι R₁.σ R₁.w s.val e) (P := P) hP
  simp only [LeAt_tr] at h
  exact h

end

theorem restHLTransport : RestHLTransport := by
  intro p n' R₁ R₂ I m lam0
  have hΨ : ∀ (c : R₁.Kf) (v : Vsp R₁.Kf lam0), PsiV I lam0 (c • v) = I.φK c • PsiV I lam0 v := by
    intro c v
    exact Subtype.ext (map_smul' _ c v.1)
  refine ⟨mapSubEquiv I.JW, PsiV I lam0, hΨ, fun L => isLattice_mapSub_iff I.JW L, fun r e => ?_, fun L x => ?_,
    fun e x => ?_, ?_⟩
  · constructor
    · exact isEdge_mapSub I.JW p n' r
    · intro h
      have h2 := isEdge_mapSub I.JW.symm p n' r h
      simp only at h2
      have h3 : mapSub I.JW.symm (mapSub I.JW e.src) = e.src := mapSub_symm _ _
      have h4 : mapSub I.JW.symm (mapSub I.JW e.tgt) = e.tgt := mapSub_symm _ _
      have h5 : (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) = e := by rw [h3, h4]
      have h6 : IsEdge p n' r (⟨mapSub I.JW.symm (mapSub I.JW e.src), mapSub I.JW.symm (mapSub I.JW e.tgt)⟩ :
          Edge R₁.W R₁.Qq (m + 1)) := h2
      rwa [h5] at h6
  · constructor
    · intro hx
      exact HLpoly_tr I lam0 L x.1 hx
    · intro hx
      have h2 := HLpoly_tr I.symm lam0 (mapSub I.JW L) (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW L) = L := mapSub_symm I.JW L
      rw [h3] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · constructor
    · intro hx
      exact HLepoly_tr I lam0 e x.1 hx
    · intro hx
      have h2 := HLepoly_tr I.symm lam0 ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩ (PsiV I lam0 x).1 hx
      have h3 : mapSub I.symm.JW (mapSub I.JW e.src) = e.src := mapSub_symm I.JW _
      have h3' : mapSub I.symm.JW (mapSub I.JW e.tgt) = e.tgt := mapSub_symm I.JW _
      simp only [h3, h3'] at h2
      have h4 : I.symm.JO.pm ((PsiV I lam0 x : Vsp R₂.Kf lam0) : MvPolynomial _ R₂.Kf) = x.1 := pm_symm I x.1
      rw [h4] at h2
      exact h2
  · unfold dimV Module.finrank
    rw [rank_eq_of_equiv_equiv I.φK (PsiV I lam0) I.φK.bijective hΨ]

theorem lpRingIndep_of' (h : RestRSIso) : LPRingIndep := lpRingIndep_of h restHLTransport

end Formalism.MainNotions.flipOneThree.Pf

end
end
