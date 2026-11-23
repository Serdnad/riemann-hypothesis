module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle207
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle208
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem l_pow_eq (n : ℕ) : ((l : K⟦X⟧)) ^ n =
    E K l e ^ n - (X : K⟦X⟧) ^ e * ∑ i ∈ Finset.range n, (l : K⟦X⟧) ^ i * E K l e ^ (n - 1 - i) := by
  have h := (Commute.all ((l : K⟦X⟧)) (E K l e)).geom_sum₂_mul n
  have hE : (l : K⟦X⟧) - E K l e = -((X : K⟦X⟧) ^ e) := by simp [E]
  rw [hE] at h
  linear_combination -h

theorem l_pow_smul (n : ℕ) (y : Vec K a ι) : (l : K) ^ n • y =
    E K l e ^ n • y - (X : K⟦X⟧) ^ e • ∑ i ∈ Finset.range n, ((l ^ i : ℕ)) • (E K l e ^ (n - 1 - i) • y : Vec K a ι) := by
  have h1 : (l : K) ^ n • y = ((l : K⟦X⟧)) ^ n • y := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h1, l_pow_eq (e := e), sub_smul, mul_smul, Finset.sum_smul]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

variable (D : BKDat O K l e a ι η H)

theorem E_pow_smul_mem_M (j : ℕ) {m : Vec K a ι} (hm : m ∈ D.M) : E K l e ^ j • m ∈ D.M := by
  have := D.M.smul_mem (EIn l e (A O K) ^ j) hm
  simpa [Subalgebra.smul_def] using this

theorem E_pow_smul_mem_EM (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η) : E K l e ^ j • y ∈ D.EM η := by
  rw [mem_divE] at hy ⊢
  rw [smul_comm]
  exact E_pow_smul_mem_M D j hy

theorem E_pow_smul_mem_Y (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.Y) : E K l e ^ j • y ∈ D.Y := by
  rw [BKDat.Y, Descent.mem_invOf] at hy ⊢
  exact ⟨E_pow_smul_mem_EM D j hy.1, fun g => by rw [Descent.act_E_pow_smul, hy.2 g]⟩

theorem cls_E_pow_smul_mem_Z (j : ℕ) {y : Vec K a ι} (hy : y ∈ D.EM η)
    (h : ∀ g, D.desc.actPol g (D.cls y) = D.cls y) : D.cls (E K l e ^ j • y) ∈ D.Z := by
  refine ⟨⟨_, E_pow_smul_mem_EM D j hy, rfl⟩, fun g => ?_⟩
  have h' := congrArg (D.mulPol ⟨_, pow_mem (E_mem l e (Rpi O K l e)) j⟩) (h g)
  rw [Descent.actPol_cls] at h'
  change D.desc.actPol g (D.cls (E K l e ^ j • y)) = D.cls (E K l e ^ j • y)
  rw [Descent.actPol_cls, Descent.act_E_pow_smul]
  exact h'

end GlobalTheory.NgalDivisible

namespace GlobalTheory.NgalDivisible

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  (D : BKDat O K l e a ι η H)

theorem l_pow_smul_Z {w : D.Pol} (hw : w ∈ D.Z) : ∃ z ∈ D.Z, (l : K) ^ η • w = D.vPol z := by
  obtain ⟨⟨y, hy, rfl⟩, h⟩ := D.desc.mem_Z.1 hw
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsZ : D.cls s ∈ D.Z := by

    rw [hs, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_nsmul]
      exact Submodule.smul_of_tower_mem _ _ (cls_E_pow_smul_mem_Z D _ hy h)
  refine ⟨-D.cls s, neg_mem hsZ, ?_⟩
  have h0 : D.cls (E K l e ^ η • y) = 0 := D.cls_eq_zero_iff.2 (D.M_le_Man hy)
  rw [← map_smul, l_pow_smul (e := e) η y, ← hs, map_sub, h0, zero_sub, map_neg, PhiMod.vPol_cls]

theorem l_pow_smul_Y {y : Vec K a ι} (hy : y ∈ D.Y) : (l : K) ^ η • y ∈ D.Y' ⊔ D.Minv := by
  have hy' := hy
  rw [BKDat.Y, Descent.mem_invOf] at hy'
  set s : Vec K a ι := ∑ i ∈ Finset.range η, (l ^ i : ℕ) • (E K l e ^ (η - 1 - i) • y : Vec K a ι) with hs
  have hsY : s ∈ D.Y := Submodule.sum_mem _ fun i _ =>
    Submodule.smul_of_tower_mem _ _ (E_pow_smul_mem_Y D _ hy)
  have h1 : -((X : K⟦X⟧) ^ e • s) ∈ D.Y' :=
    D.desc.mem_Y'.2 ⟨-s, neg_mem hsY, smul_neg _ _⟩
  have h2 : E K l e ^ η • y ∈ D.Minv := by
    rw [BKDat.Minv, Descent.mem_invOf]
    exact ⟨hy'.1, fun g => by rw [Descent.act_E_pow_smul, hy'.2 g]⟩
  rw [l_pow_smul (e := e) η y, ← hs, sub_eq_neg_add]
  exact Submodule.add_mem_sup h1 h2

end GlobalTheory.NgalDivisible

theorem GlobalTheory.divisible_of_BKDat : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Divisible D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨fun _ hw => NgalDivisible.l_pow_smul_Z D hw, fun _ hy => NgalDivisible.l_pow_smul_Y D hy⟩
end

section

open PowerSeries GlobalTheory.BK Matrix

noncomputable section

namespace GlobalTheory.IntegralityComp

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem S_eq_A_add_Fil {j : ℕ} (hj : j < l) {f : K⟦X⟧} (hf : f ∈ S O K e) :
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration O K l e j hj f hf

theorem Fil_le_E_pow (j : ℕ) {φ : S O K e} (hφ : φ ∈ Fil O K l e j) :
    ∃ q ∈ Rpi O K l e, (φ : K⟦X⟧) = E K l e ^ j * q := GlobalTheory.T.mem_eisensteinFiltration_eq_eisenstein_pow_mul_disc O K l e j φ hφ

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def colVec (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : Vec K a ι := Pi.single τ ((P.mx τ).col i)

theorem colVec_mem_MM (P : PhiMod O K l e a ι) (τ : ZMod a) (i : ι) : colVec P τ i ∈ P.MM := by
  refine mem_tot.2 fun σ => ?_
  by_cases h : σ = τ
  · subst h
    simp only [colVec, Pi.single_eq_same]
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp only [colVec, Pi.single_eq_of_ne h]
    exact zero_mem _

theorem sum_colVec (P : PhiMod O K l e a ι) (c : ZMod a → ι → K⟦X⟧) :
    (∑ τ, ∑ i, c τ i • colVec P τ i) = fun τ => P.mx τ *ᵥ c τ := by
  ext τ k
  simp only [Finset.sum_apply, Pi.smul_apply, colVec, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · simp [Matrix.mulVec, dotProduct, mul_comm]
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem MM_eq_L_add_FilMM (P : PhiMod O K l e a ι) {j : ℕ} (hj : j < l) {m : Vec K a ι}
    (hm : m ∈ P.MM) : ∃ p ∈ P.L, ∃ f ∈ P.FilMM j, m = p + f := by
  have hs (τ : ZMod a) (i : ι) : (P.mxInv τ *ᵥ m τ) i ∈ S O K e :=
    P.mem_extc_iff.1 (mem_tot.1 hm τ) i
  choose g hg φ hφ hgφ using fun τ i => S_eq_A_add_Fil (O := O) (l := l) hj (hs τ i)
  have hm' (τ : ZMod a) : m τ = P.mx τ *ᵥ (P.mxInv τ *ᵥ m τ) := by
    rw [Matrix.mulVec_mulVec, P.mx_mul_mxInv, Matrix.one_mulVec]
  refine ⟨fun τ => P.mx τ *ᵥ g τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨g τ, fun i => hg τ i, rfl⟩,
    ∑ τ, ∑ i, φ τ i • colVec P τ i, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem_smul (hφ τ i) (colVec_mem_MM P τ i)
  · have : (∑ τ, ∑ i, φ τ i • colVec P τ i) = ∑ τ, ∑ i, (φ τ i : K⟦X⟧) • colVec P τ i := rfl
    rw [this, sum_colVec]
    ext1 τ
    rw [Pi.add_apply, ← Matrix.mulVec_add, hm' τ]
    congr 1
    ext1 i
    exact hgφ τ i

section Dat

variable [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

theorem Ezpow_smul_FilMM_mem (hηH : η < H) {f : Vec K a ι} (hf : f ∈ D.FilMM (10 * H)) :
    Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man := by
  refine Submodule.smul_induction_on hf (fun φ hφ m hm => ?_) (fun x y hx hy => ?_)
  · obtain ⟨q, hq, hφq⟩ := Fil_le_E_pow (O := O) (10 * H) hφ
    have hEm := D.smul_mem_Mext (A_le_S l e) hm
    have key : Ezpow K l e (-(2 * H : ℤ)) • φ • m =
        (E K l e ^ (8 * H - η) * q) • (E K l e ^ η • m) := by
      have h1 : Ezpow K l e (-(2 * H : ℤ)) * E K l e ^ (10 * H) = E K l e ^ (8 * H - η) * E K l e ^ η := by
        rw [← pow_add, show 8 * H - η + η = 8 * H by omega, ← Ezpow_natCast, ← Ezpow_natCast,
          ← Ezpow_add]
        congr 1
        push_cast
        ring
      rw [show φ • m = (φ : K⟦X⟧) • m from rfl, hφq, smul_smul, smul_smul, ← mul_assoc, h1]
      congr 1
      ring
    rw [key]
    exact D.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) _) hq)
      (D.Mext_mono (S_le_R l e) hEm)
  · rw [smul_add]
    exact add_mem hx hy

theorem E_pow_smul_EN_mem (hηH : η < H) (hl : 10 * H + 2 ≤ l) {y : Vec K a ι} (hy : y ∈ D.EM η) :
    ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), E K l e ^ (2 * H) • D.EN y = p + f := by
  have hl0 : E K l e ^ (H + η) • y ∈ D.L := by
    rw [pow_add, mul_smul]
    exact D.lower _ hy
  have hMM : E K l e ^ (H + η) • y ∈ D.MM := D.ext_mono (A_le_S l e) hl0
  have hc : D.conn (E K l e ^ (H + η) • y) ∈ D.MM := D.conn_mem_MM hMM
  have hA : E K l e ^ (H - η) * E K l e ∈ S O K e := mul_mem (pow_mem (E_mem l e _) _) (E_mem l e _)
  obtain ⟨p, hp, f, hf, hpf⟩ := MM_eq_L_add_FilMM D.toPhiMod (j := 10 * H) (by omega)
    (D.MM.smul_mem ⟨_, hA⟩ hc)
  have hB : E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e)) ∈ A O K :=
    mul_mem (pow_mem (E_mem l e _) _) (mul_mem (natCast_mem _ _) (by
      rw [N_E]; exact mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _)))
  refine ⟨p - (E K l e ^ (H - η) * (((H + η : ℕ) : K⟦X⟧) * N K (E K l e))) • (E K l e ^ (H + η) • y),
    sub_mem hp (D.L.smul_mem ⟨_, hB⟩ hl0), f, hf, ?_⟩
  have h1 : E K l e ^ (2 * H) • D.EN y = E K l e ^ (H - η) • (E K l e ^ (H + η) • D.EN y) := by
    rw [smul_smul, ← pow_add, show H - η + (H + η) = 2 * H by omega]
  rw [h1, PhiMod.E_pow_smul_EN, PhiMod.EN_apply, smul_sub, smul_smul, smul_smul]
  have h2 : (E K l e ^ (H - η) * E K l e) • D.conn (E K l e ^ (H + η) • y) = p + f := hpf
  rw [h2]
  abel

end Dat

end GlobalTheory.IntegralityComp

theorem GlobalTheory.IntegralityComp.integralityComputation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.IntegralityComputation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  exact ⟨fun m hm => GlobalTheory.IntegralityComp.MM_eq_L_add_FilMM D.toPhiMod (by omega) hm,
    fun f hf => GlobalTheory.IntegralityComp.Ezpow_smul_FilMM_mem D hηH hf,
    fun y hy => GlobalTheory.IntegralityComp.E_pow_smul_EN_mem D hηH hl hy⟩
end
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds in
theorem degrees_eq_image_pairs {e : ℕ} (Sig : Finset (ZMod e)) (c : ZMod e) (m m' : ℕ) :
    degrees Sig c m m' =
      ((Sig.image fun s => (c - s).val) ×ˢ Finset.Ico m m').image (fun p : ℕ × ℕ => p.1 + p.2 * e) := by
  ext i
  simp only [degrees, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, n, ⟨hs, hn⟩, rfl⟩
    exact ⟨(c - s).val, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
  · rintro ⟨x, n, ⟨⟨s, hs, rfl⟩, hn⟩, rfl⟩
    exact ⟨s, n, ⟨hs, hn⟩, rfl⟩

theorem add_mul_inj_of_lt {e x y n m : ℕ} (hx : x < e) (hy : y < e) (h : x + n * e = y + m * e) :
    x = y ∧ n = m := by
  have h1 : (x + n * e) % e = x := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
  have h2 : (y + m * e) % e = y := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  have hxy : x = y := by rw [← h1, ← h2, h]
  subst hxy
  have he : 0 < e := lt_of_le_of_lt (Nat.zero_le _) hx
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right he (by omega)⟩

end GlobalTheory

namespace GlobalTheory

theorem exists_period_dvd {l e a : ℕ} (ha : 1 ≤ a) (he : e + 1 = l ^ a) [NeZero e]
    (Sig : Finset (ZMod e)) (c : ZMod e) {s s' : ZMod e} (hs : s ∈ Sig) (hs' : s' ∈ Sig) :
    ∃ ρ, 1 ≤ ρ ∧ ρ ≤ GlobalTheory.BK.maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((((c - s).val : ℕ) : ℤ) - (((c - s').val : ℕ) : ℤ)) * ((l : ℤ) ^ ρ - 1) := by
  have hla : ((l : ZMod e)) ^ a = 1 := by
    have h := congrArg (Nat.cast : ℕ → ZMod e) he
    push_cast at h
    rw [ZMod.natCast_self, zero_add] at h
    exact h.symm
  have hper : Function.IsPeriodicPt (fun x : ZMod e => (l : ZMod e) * x) a (s' - s) := by
    show (fun x : ZMod e => (l : ZMod e) * x)^[a] (s' - s) = s' - s
    rw [mul_left_iterate, hla]; exact one_mul _
  refine ⟨GlobalTheory.BK.frobPeriod l (s' - s), hper.minimalPeriod_pos (by omega), ?_, ?_⟩
  · exact Finset.le_sup (f := fun p : ZMod e × ZMod e => GlobalTheory.BK.frobPeriod l (p.1 - p.2)) (b := (s', s))
      (Finset.mem_product.2 ⟨hs', hs⟩)
  · have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
      have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
      linarith
    rw [hE, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hfix : (fun x : ZMod e => (l : ZMod e) * x)^[GlobalTheory.BK.frobPeriod l (s' - s)] (s' - s) = s' - s :=
      Function.iterate_minimalPeriod
    rw [mul_left_iterate] at hfix
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination hfix

end GlobalTheory

namespace GlobalTheory


open GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds GlobalTheory.BK in
theorem lagrange_C_rho_eq_comb_degrees : ∀ (l e a : ℕ) [Fact l.Prime], 1 ≤ a → e + 1 = l ^ a →
    ∀ (Sig : Finset (ZMod e)) (c : ZMod e) (A' N : ℕ), Sig.card ≤ N → 2 * A' + 2 < l →
    ∃ α β : Polynomial ℤ_[l], Polynomial.C ((l : ℤ_[l]) ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) =
      α * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₁ Sig c A').map (Int.castRingHom ℤ_[l]) +
        β * (GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.P₂ Sig c A').map (Int.castRingHom ℤ_[l]) := by
  intro l e a _ ha he Sig c A' N hN hA
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hepos : 0 < e := by
    have : l ≤ l ^ a := Nat.le_self_pow (by omega) l
    omega
  have : NeZero e := ⟨by omega⟩
  have hE : ((l : ℤ) ^ a - 1) = (e : ℤ) := by
    have : (e : ℤ) + 1 = (l : ℤ) ^ a := by exact_mod_cast he
    linarith
  set Cc : Finset ℕ := Sig.image fun s => (c - s).val with hCc
  have hCclt : ∀ x ∈ Cc, x < e := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.1 hx
    exact ZMod.val_lt _
  have hD₁ : D₁ Sig c A' = (Cc ×ˢ Finset.Ico 0 A').image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c 0 A'
  have hD₂ : D₂ Sig c A' = (Cc ×ˢ Finset.Ico A' (2 * A')).image (fun p : ℕ × ℕ => p.1 + p.2 * e) :=
    degrees_eq_image_pairs Sig c A' (2 * A')
  have hmap : ∀ T : Finset ℕ, (rootPoly T).map (Int.castRingHom ℤ_[l]) =
      ∏ i ∈ T.image (Nat.cast : ℕ → ℤ), (Polynomial.X - Polynomial.C ((i : ℤ) : ℤ_[l])) := by
    intro T
    rw [Finset.prod_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    simp [rootPoly, Polynomial.map_prod]
  set Z₁ : Finset ℤ := (D₁ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₁
  set Z₂ : Finset ℤ := (D₂ Sig c A').image (Nat.cast : ℕ → ℤ) with hZ₂
  have hdisj : Disjoint Z₁ Z₂ := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hi1
    obtain ⟨i₂, hi₂, heq⟩ := Finset.mem_image.1 hi2
    have heq' : i₂ = i₁ := by exact_mod_cast heq
    subst heq'
    rw [hD₁] at hi₁
    rw [hD₂] at hi₂
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.1 hi₁
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hi₂
    rw [Finset.mem_product, Finset.mem_Ico] at hp hq
    have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) (hpe.trans hqe.symm)
    omega
  have hlt : ∀ x ∈ Cc, x < l ^ a - 1 := fun x hx => by have := hCclt x hx; omega
  have hper : ∀ x ∈ Cc, ∀ y ∈ Cc, x ≠ y → ∃ ρ, 1 ≤ ρ ∧ ρ ≤ maxPeriod l Sig ∧
      ((l : ℤ) ^ a - 1) ∣ ((x : ℤ) - y) * ((l : ℤ) ^ ρ - 1) := by
    intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.1 hy
    exact exists_period_dvd ha he Sig c hs hs'
  have hU : Z₁ ∪ Z₂ = ((Cc ×ˢ Finset.range (2 * A')).image
      (fun p : ℕ × ℕ => p.1 + p.2 * e)).image (Nat.cast : ℕ → ℤ) := by
    rw [hZ₁, hZ₂, ← Finset.image_union, hD₁, hD₂, ← Finset.image_union, ← Finset.product_union]
    congr 3
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    omega
  have hbound : ∀ i ∈ Z₁, (∑ j ∈ Z₂, padicValInt l (i - j)) +
      ∑ j ∈ Z₁.erase i, padicValInt l (i - j) ≤ rho l Sig N := by
    intro i hi
    rw [Finset.sum_erase _ (by simp), add_comm, ← Finset.sum_union hdisj, hU,
      Finset.sum_image (fun x _ y _ hxy => by exact_mod_cast hxy)]
    rw [Finset.sum_image (fun p hp q hq hpq => by
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have := add_mul_inj_of_lt (hCclt _ hp.1) (hCclt _ hq.1) hpq
      exact Prod.ext this.1 this.2), Finset.sum_product]
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hi
    rw [hD₁] at hi₀
    obtain ⟨⟨x, n⟩, hxn, rfl⟩ := Finset.mem_image.1 hi₀
    rw [Finset.mem_product, Finset.mem_Ico] at hxn
    have LB := Formalism.IrreducibleCountingLemmas.WindowSums.sumPadicValDifferencesLe l a A' (maxPeriod l Sig) Cc hl ha (by omega) hlt
      hper x hxn.1 n hxn.2.2
    rw [hE] at LB
    refine le_trans (le_of_eq ?_) (LB.trans ?_)
    · refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc
        simp
      · push_cast
        rfl
    · have hcard : Cc.card ≤ N := Finset.card_image_le.trans hN
      unfold rho
      calc (Cc.card - 1) * maxPeriod l Sig ≤ (N - 1) * maxPeriod l Sig :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 * (N - 1) * maxPeriod l Sig := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (Formalism.IrreducibleCountingLemmas.WindowSums.lagrange_resolvent_T l Z₁ Z₂ (rho l Sig N) hdisj hbound)
  refine ⟨α, β, ?_⟩
  rw [← hαβ, P₁, P₂, hmap, hmap]

end GlobalTheory
end

section

namespace GlobalTheory.SpanMapTop

theorem map_mem_span {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (M : Matrix (Fin r) (Fin r) A)
    (hM : M ∈ Submodule.span A (Set.range f)) :
    M.map (algebraMap A B) ∈
      Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero =>
    have : (0 : Matrix (Fin r) (Fin r) A).map (algebraMap A B) = 0 := by
      ext i j; simp
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : (x + y).map (algebraMap A B) = x.map (algebraMap A B) + y.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : (a • x).map (algebraMap A B) = (algebraMap A B a) • x.map (algebraMap A B) := by
      ext i j; simp
    rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_map_eq_top {Γ A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r : ℕ}
    (f : Γ → Matrix (Fin r) (Fin r) A) (h : Submodule.span A (Set.range f) = ⊤) :
    Submodule.span B (Set.range fun g => (f g).map (algebraMap A B)) = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h1 := map_mem_span (B := B) f (Matrix.single i j 1) (h ▸ Submodule.mem_top)
  have h2 : Matrix.single i j (M i j) =
      M i j • (Matrix.single i j (1 : A)).map (algebraMap A B) := by
    ext a b
    simp only [Matrix.single, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [h2]
  exact Submodule.smul_mem _ _ h1

theorem span_mapRep_eq_top {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ} {B : Type} [CommRing B]
    [Algebra A B] {ρ : Γ →* GL (Fin r) A}
    (h : Submodule.span A (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ)) = ⊤) :
    Submodule.span B
      (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (algebraMap A B) ρ))) = ⊤ :=
  span_map_eq_top (B := B) (fun g => GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat ρ g) h

end GlobalTheory.SpanMapTop
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jHyp_mem_induced_fourier_weyl : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧ ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  first | exact @GlobalTheory.JR.HypJ.main | exact GlobalTheory.JR.HypJ.main | (intros; apply GlobalTheory.JR.HypJ.main <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.integral_psiK_over_scaled_integers_eq_volume_indicator : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ c : F, c ≠ 0 → ∀ b : A.K, ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * b) ∂μK = Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => ((μK {z : A.K | c • z ∈ A.OK}).toReal : ℂ)) b := by
  first | exact @GlobalTheory.JR.charIntegral_inv_OK | exact GlobalTheory.JR.charIntegral_inv_OK | (intros; apply GlobalTheory.JR.charIntegral_inv_OK <;> assumption)
end
