module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle092
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.PhiRootVal

def RootOrZero {K : Type} [Field K] (z : K) : Prop := z = 0 ∨ ∃ n : ℕ, 0 < n ∧ z ^ n = 1

variable {K : Type} [Field K]

theorem RootOrZero.zero : RootOrZero (0 : K) := Or.inl rfl

theorem RootOrZero.one : RootOrZero (1 : K) := Or.inr ⟨1, one_pos, one_pow 1⟩

theorem RootOrZero.mul {z w : K} (hz : RootOrZero z) (hw : RootOrZero w) : RootOrZero (z * w) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl (zero_mul w)
  rcases hw with rfl | ⟨m, hm, hw⟩
  · exact Or.inl (mul_zero z)
  refine Or.inr ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [mul_pow, pow_mul, hz, one_pow, one_mul, mul_comm n m, pow_mul, hw, one_pow]

theorem RootOrZero.inv {z : K} (hz : RootOrZero z) : RootOrZero z⁻¹ := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · exact Or.inl inv_zero
  exact Or.inr ⟨n, hn, by rw [inv_pow, hz, inv_one]⟩

theorem RootOrZero.prod {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, RootOrZero (f i)) :
    RootOrZero (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (RootOrZero.one : RootOrZero (1 : K))
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem RootOrZero.intOff {z : K} (hz : RootOrZero z) (σ : K →+* ℂ) (S : Finset ℕ) : IntOff S (σ z) := by
  rcases hz with rfl | ⟨n, hn, hz⟩
  · rw [map_zero]; exact IntOff.zero
  exact IntOff.of_pow hn (by rw [← map_pow, hz, map_one])

theorem addChar_root {A : Type} [AddCommGroup A] [Finite A] (ψ : AddChar A K) (a : A) : RootOrZero (ψ a) := by
  refine Or.inr ⟨Nat.card A, Nat.card_pos, ?_⟩
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]

theorem hom_root {G : Type} [Group G] [Finite G] (χ : G →* Kˣ) (g : G) : RootOrZero ((χ g : Kˣ) : K) := by
  refine Or.inr ⟨Nat.card G, Nat.card_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_root (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) : RootOrZero (LocE.unitV χ a) := by
  unfold LocE.unitV
  split_ifs with h
  · exact hom_root χ _
  · exact RootOrZero.zero

end Loc
end GlobalTheory.PhiRootVal

namespace GlobalTheory.PhiRootVal
variable {K : Type} [Field K]
section Loc2
variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem phiQ_root (q : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    RootOrZero (LocE.PhiQ q ξ k₀ r c' n' c n x) := by
  unfold LocE.PhiQ
  split_ifs
  · exact unitV_root ξ _
  · exact RootOrZero.zero

theorem lamGv_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGv ψ₀ χ r t j M) := by
  unfold LocE.lamGv
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem lamGvS_root (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r t j : ℕ) (M : ℕ → ℕ → E) :
    RootOrZero (LocE.lamGvS ψ₀ χ k₀ r t j M) := by
  unfold LocE.lamGvS
  exact (addChar_root ψ₀ _).mul (RootOrZero.prod _ _ fun i _ => unitV_root (χ i) _)

theorem phiG_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    (k₀ r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiG q ψ₀ χ sharp k₀ r t j c' n' c n x) := by
  unfold LocE.PhiG
  dsimp only
  split_ifs
  · exact (lamGv_root ψ₀ χ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

theorem phiGS_root (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x) : RootOrZero (LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x) := by
  unfold LocE.PhiGS
  dsimp only
  split_ifs
  · exact (lamGvS_root ψ₀ χ _ _ _ _ _).mul (unitV_root _ _).inv
  · exact RootOrZero.zero

end Loc2

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiAt_root (sharp : Bool) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiAt (R := R) Ch mu sharp i P x) := by
  unfold PhiAt
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

theorem phiTop_root (sharp : Bool) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (x) :
    RootOrZero (PhiTop (R := R) Ch mu sharp m2 P x) := by
  unfold PhiTop
  split_ifs
  · exact phiGS_root (x := x) ..
  · exact phiG_root (x := x) ..
  · exact phiQ_root (x := x) ..

end Chain

theorem phi_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ (P : HeightOneSpectrum (𝓞 t.X.E)), (∀ (i : ℕ) x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiAt (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp i P x))) ∧ ∀ x, IntOff (t.O u μ).S (t.seam.σ₀ (PhiTop (R := D.R) t.Ch (t.tup μ) (t.cst μ).sharp t.m2 P x)) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  exact ⟨fun i x => (phiAt_root _ _ _ _ _ x).intOff _ _, fun x => (phiTop_root _ _ _ _ _ x).intOff _ _⟩

end GlobalTheory.PhiRootVal
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopFirstRow

theorem two_w_le_first_row : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  refine ⟨max x1 (max x2 x3), fun x hx hx1 i u j hj z hz => ?_⟩
  have hxa : x ≥ x1 := le_trans (le_max_left _ _) hx
  have hxb : x ≥ x2 := le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx
  have hxc : x ≥ x3 := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := h1 x hxa hx1 i
  obtain ⟨e1, e2, e3, -⟩ := h2 x hxb hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := h3 x hxc hx1 i j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dite_eq_left hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dite_eq_left hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

end GlobalTheory.TopFirstRow
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ExcessLow

theorem excess_sum (f : ℕ → ℝ) (k M : ℕ) (w N S η W : ℝ) (hk : 2 ≤ k) (hN1 : 1 ≤ N) (hS : 0 ≤ S)
    (hlong : ∀ r < k, w - N - 1 / 2 < f r ∧ f r < w + (if r = 0 then 3 * S else S))
    (hblock : ∀ r, k ≤ r → r < k + M → 0 ≤ f r ∧ f r ≤ η)
    (hkN : (k : ℝ) * N ≤ S / 4) (hkS : (k : ℝ) * S ≤ W) (hM : (M : ℝ) * η ≤ W) (hW : W ≤ w) :
    0 ≤ ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ∧
      ∑ r ∈ Finset.range (k + M), f r - ((k : ℝ) - 1) * w ≤ 4 * w := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Finset.sum_range_add]
  have b0 : 0 ≤ ∑ r ∈ Finset.range M, f (k + r) :=
    Finset.sum_nonneg fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).1
  have b1 : ∑ r ∈ Finset.range M, f (k + r) ≤ M * η := by
    have := Finset.sum_le_card_nsmul (Finset.range M) (fun r => f (k + r)) η fun r hr =>
      (hblock _ (by omega) (by have := Finset.mem_range.1 hr; omega)).2
    simpa using this
  have l0 : (k : ℝ) * (w - N - 1 / 2) ≤ ∑ r ∈ Finset.range k, f r := by
    have := Finset.card_nsmul_le_sum (Finset.range k) f (w - N - 1 / 2) fun r hr =>
      (hlong r (Finset.mem_range.1 hr)).1.le
    simpa only [Finset.card_range, nsmul_eq_mul] using this
  have l1 : ∑ r ∈ Finset.range k, f r ≤ k * (w + S) + 2 * S := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have h0 := (hlong 0 (by omega)).2
    rw [if_pos rfl] at h0
    have h1 := Finset.sum_le_card_nsmul (Finset.range k') (fun r => f (r + 1)) (w + S) fun r hr => by
      have := (hlong (r + 1) (by have := Finset.mem_range.1 hr; omega)).2
      rw [if_neg (by omega)] at this
      exact this.le
    simp only [Finset.card_range, nsmul_eq_mul] at h1
    push_cast
    nlinarith
  have h2S : 2 * S ≤ k * S := mul_le_mul_of_nonneg_right hk' hS
  have hkN1 : (k : ℝ) ≤ k * N := le_mul_of_one_le_right (by linarith) hN1
  constructor
  · nlinarith
  · nlinarith

theorem excess_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max x1 x2) (max x3 x4), fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hx
  obtain ⟨a1, a2, a3, -⟩ := h1 x e1 hx1 i
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (h3 x e3 hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => h4 x e4 hx1 i u j hj z r hr hr') a1 a2 ?_ (h2 x e2 hx1 i j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

end GlobalTheory.ExcessLow
end

section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.TopExcess

theorem sum_range_split (f : ℕ → ℝ) (k M : ℕ) (hk : 2 ≤ k) :
    ∑ r ∈ Finset.range (k + M), f r =
      f 0 + ∑ r ∈ Finset.Ico 1 (k - 1), f r + f (k - 1) + ∑ r ∈ Finset.Ico k (k + M), f r := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← Finset.sum_range_add_sum_Ico f (Nat.le_add_right (n + 1) M), Finset.sum_range_succ,
    ← Finset.sum_range_add_sum_Ico f (by omega : 1 ≤ n), Finset.sum_range_one]

theorem sum_Ico_bounds (f : ℕ → ℝ) (a b : ℕ) (lo hi : ℝ) (h : ∀ r, a ≤ r → r < b → lo ≤ f r ∧ f r ≤ hi) :
    ((b - a : ℕ) : ℝ) * lo ≤ ∑ r ∈ Finset.Ico a b, f r ∧ ∑ r ∈ Finset.Ico a b, f r ≤ ((b - a : ℕ) : ℝ) * hi := by
  constructor
  · have := Finset.card_nsmul_le_sum (Finset.Ico a b) f lo
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).1)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this
  · have := Finset.sum_le_card_nsmul (Finset.Ico a b) f hi
      (fun r hr => (h r (Finset.mem_Ico.1 hr).1 (Finset.mem_Ico.1 hr).2).2)
    rwa [Nat.card_Ico, nsmul_eq_mul] at this

theorem top_excess : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.ShNums.size_rel Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x3, h3⟩ := GlobalTheory.LongRows.longRows Fm
  obtain ⟨x4, h4⟩ := GlobalTheory.TopRows.top_rows Fm
  obtain ⟨x5, h5⟩ := GlobalTheory.blockRows_mem_Icc Fm
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, fun x hx hx1 i u j hj z hz => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨⟨⟨g1, g2⟩, g3, g4⟩, g5⟩ := hx
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := h1 x g1 hx1 i
  obtain ⟨b1, -, b3⟩ := h2 x g2 hx1 i j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := h3 x g3 hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := h4 x g4 hx1 i u j hj z hz
  have e := h5 x g5 hx1 i u j hj z
  clear h1 h2 h3 h4 h5
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

end GlobalTheory.TopExcess
end
