module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle035
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
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
import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth

variable {R : Type} [CommRing R]

theorem red_add' (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j
  simp [red]

theorem red_neg' (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (-x) = -red ϖ k x := by
  ext i j
  simp [red]

theorem cT_add' (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j
  simp [cT]

theorem cT_neg' (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    cT σ (-x) = -cT σ x := by
  ext i j
  simp [cT]

theorem cT_single' (σ : R →+* R) {n : ℕ} (i j : Fin n) (c : R) :
    cT σ (Matrix.single i j c) = Matrix.single j i (σ c) := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_single, Matrix.transpose_single]

theorem trace_single_mul' {n : ℕ} (i j : Fin n) (c : R) (y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (Matrix.single i j c * y) = c * y j i := by
  rw [Matrix.trace_single_mul, smul_eq_mul]

theorem trace_red_mul (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by
  unfold PositivityTheory.PfSWUS.Loc.red
  rw [← Matrix.map_mul]

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]

theorem tsum_eq_zero_of_shift {G : Type} [AddCommGroup G] (H : Set G)
    (hadd : ∀ a b, a ∈ H → b ∈ H → a + b ∈ H) (hneg : ∀ a, a ∈ H → -a ∈ H)
    (f : G → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) (B₀ : G) (hB₀ : B₀ ∈ H) (h : f B₀ ≠ 1) :
    ∑' B : H, f B.1 = 0 := by
  let e : H ≃ H :=
    { toFun := fun B => ⟨B₀ + B.1, hadd _ _ hB₀ B.2⟩
      invFun := fun B => ⟨-B₀ + B.1, hadd _ _ (hneg _ hB₀) B.2⟩
      left_inv := fun B => Subtype.ext (by simp)
      right_inv := fun B => Subtype.ext (by simp) }
  have key : ∑' B : H, f B.1 = f B₀ * ∑' B : H, f B.1 := by
    calc ∑' B : H, f B.1 = ∑' B : H, f (e B).1 := (e.tsum_eq (fun B : H => f B.1)).symm
      _ = ∑' B : H, f B₀ * f B.1 := tsum_congr fun B => by
          show f (B₀ + B.1) = _
          exact hf _ _
      _ = f B₀ * ∑' B : H, f B.1 := tsum_mul_left
  have hzero : (f B₀ - 1) * ∑' B : H, f B.1 = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  rcases mul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'

theorem hermMod_add {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a b : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k)
    (hb : b ∈ hermMod σ ϖ n k) : a + b ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha hb ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  have hb'' : PositivityTheory.PfSWUS.Loc.cT σ b' = b' := hb'
  refine ⟨a' + b', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_add' _ _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (a' + b') = a' + b'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', ha'', hb'']

theorem hermMod_neg {σ : R →+* R} {ϖ : R} {n k : ℕ}
    (a : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (ha : a ∈ hermMod σ ϖ n k) :
    -a ∈ hermMod σ ϖ n k := by
  unfold PositivityTheory.PfSWUS.Loc.hermMod at ha ⊢
  obtain ⟨a', ha', rfl⟩ := ha
  have ha'' : PositivityTheory.PfSWUS.Loc.cT σ a' = a' := ha'
  refine ⟨-a', ?_, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_neg' _ _ _⟩
  show PositivityTheory.PfSWUS.Loc.cT σ (-a') = -a'
  rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_neg', ha'']

theorem red_eq_zero_of_trivial {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ)
    (n k : ℕ) (y : Matrix (Fin n) (Fin n) R) (hy : cT σ y = y)
    (h : ∀ b : Matrix (Fin n) (Fin n) R, cT σ b = b →
      ψ k (Ideal.Quotient.mk _ (Matrix.trace (b * y))) = 1) :
    red ϖ k y = 0 := by
  have hσσ : ∀ a, σ (σ a) = a := hR.1
  ext i j
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_apply, Matrix.zero_apply]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply GlobalTheory.CompanionTheory.SiegLoc.trace_nondeg hR hψ k (y i j)
  intro t
  have hyji : σ (y i j) = y j i := by
    have hentry := congrFun (congrFun hy j) i
    simpa [PositivityTheory.PfSWUS.Loc.cT] using hentry
  have hb : PositivityTheory.PfSWUS.Loc.cT σ (Matrix.single j i t + Matrix.single i j (σ t)) =
      Matrix.single j i t + Matrix.single i j (σ t) := by
    rw [GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_add', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single', GlobalTheory.CompanionTheory.SiegLoc.HermOrth.cT_single',
      hσσ, add_comm]
  have htr := h _ hb
  rw [Matrix.add_mul, Matrix.trace_add, GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul',
    GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_single_mul'] at htr
  rw [map_mul σ, hyji]
  exact htr

theorem orth_hermMod (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)]
    (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (hψ : IsLevelChars σ ϖ ψ) (n k : ℕ)
    (Y : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hY : Y ∈ hermMod σ ϖ n k) :
    (Y = 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) =
        (Nat.card (hermMod σ ϖ n k) : ℂ)) ∧
      (Y ≠ 0 → (∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (B.1 * Y))) = 0) := by
  refine ⟨fun h0 => ?_, fun hne => ?_⟩
  · subst h0
    simp only [Matrix.mul_zero, Matrix.trace_zero, AddChar.map_zero_eq_one]
    rw [tsum_const, nsmul_eq_mul, mul_one]
  · have hY' := hY
    unfold PositivityTheory.PfSWUS.Loc.hermMod at hY'
    obtain ⟨y, hy, rfl⟩ := hY'
    by_contra hsum
    apply hne
    apply GlobalTheory.CompanionTheory.SiegLoc.HermOrth.red_eq_zero_of_trivial hR hψ n k y hy
    intro b hb
    rw [← GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul]
    by_contra hb1
    exact hsum (GlobalTheory.CompanionTheory.SiegLoc.HermOrth.tsum_eq_zero_of_shift _
      (fun a₁ a₂ h₁ h₂ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_add a₁ a₂ h₁ h₂)
      (fun a₁ h₁ => GlobalTheory.CompanionTheory.SiegLoc.HermOrth.hermMod_neg a₁ h₁)
      (fun B => ψ k (Matrix.trace (B * PositivityTheory.PfSWUS.Loc.red ϖ k y)))
      (fun a₁ a₂ => by simp only [Matrix.add_mul, Matrix.trace_add, AddChar.map_add_eq_mul])
      (PositivityTheory.PfSWUS.Loc.red ϖ k b) ⟨b, hb, rfl⟩ hb1)

end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
end

section

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.PatGrp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

def Supp (Φ : ι → ι → Prop) (N : Matrix ι ι K) : Prop := ∀ i j, N i j ≠ 0 → Φ i j

theorem mem_patSet_iff (h : IsPat Φ) (u : GL ι K) :
    u ∈ patSet (K := K) Φ ↔ Supp Φ ((u : Matrix ι ι K) - 1) := by
  unfold patSet
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu i j hN
    by_contra hΦ
    apply hN
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]
  · intro hS i j
    refine ⟨fun hij => ?_, fun hij hΦ => ?_⟩
    · subst hij
      have h0 : ((u : Matrix ι ι K) - 1) i i = 0 := by
        by_contra hne
        exact h.1 i (hS i i hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0
    · have h0 : ((u : Matrix ι ι K) - 1) i j = 0 := by
        by_contra hne
        exact hΦ (hS i j hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h0

theorem Supp.mul (h : IsPat Φ) {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) :
    Supp Φ (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))

theorem Supp.add {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) : Supp Φ (A + B) := by
  intro i j hij
  by_cases ha : A i j = 0
  · apply hB
    intro hb
    apply hij
    rw [Matrix.add_apply, ha, hb, add_zero]
  · exact hA i j ha

theorem det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]

def patSubgroup (h : IsPat Φ) : Subgroup (GL ι K) :=
  let M : Submonoid (GL ι K) :=
    { carrier := patSet (K := K) Φ
      mul_mem' := by
        intro u v hu hv
        have hu' := (mem_patSet_iff h u).1 hu
        have hv' := (mem_patSet_iff h v).1 hv
        refine (mem_patSet_iff h _).2 ?_
        have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
            ((u : Matrix ι ι K) - 1) + ((v : Matrix ι ι K) - 1) +
              ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) := by
          rw [Units.val_mul]
          noncomm_ring
        rw [e]
        exact (hu'.add hv').add (hu'.mul h hv')
      one_mem' := by
        refine (mem_patSet_iff h _).2 ?_
        intro i j hij
        simp at hij }
  { M with
    inv_mem' := by
      intro u hu
      have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
      have : u⁻¹ = u ^ (orderOf u - 1) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, pow_orderOf_eq_one])
      rw [this]
      exact M.pow_mem hu _ }


open Classical in
noncomputable def fill (Φ : ι → ι → Prop) (f : {p : ι × ι // Φ p.1 p.2} → K) : Matrix ι ι K := by
  classical
  exact fun i j => if h : Φ i j then f ⟨(i, j), h⟩ else 0

theorem supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by
  intro i j hij
  by_contra hΦ
  apply hij
  simp [fill, hΦ]

theorem card_patSet (h : IsPat Φ) :
    (patSet (K := K) Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} := by
  classical
  have hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det := fun f => by
    rw [det_one_add h (supp_fill f)]
    exact isUnit_one
  let e : patSet (K := K) Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K) :=
    { toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by
        refine (mem_patSet_iff h _).2 ?_
        show Supp Φ ((1 + fill Φ f) - 1)
        rw [add_sub_cancel_left]
        exact supp_fill f⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)
        ext i j
        have hu := (show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧
          (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j
        rw [Matrix.add_apply]
        simp only [fill]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, dite_eq_right (h.1 i), add_zero, hu.1 rfl]
        · rw [Matrix.one_apply_ne hij, zero_add]
          by_cases hΦ : Φ i j
          · rw [dite_eq_left hΦ]
          · rw [dite_eq_right hΦ, hu.2 hij hΦ]
      right_inv := fun f => by
        funext p
        show (1 + fill Φ f) p.1.1 p.1.2 = f p
        have hne : p.1.1 ≠ p.1.2 := fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)
        rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
        simp only [fill]
        rw [dite_eq_left p.2] }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]

end GlobalTheory.CompanionTheory.PatGrp
end
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.absolutely_integrally_closed_of_newton : ∀ {S : Type} [CommRing S] (ϖ : S) [IsAdicComplete (Ideal.span {ϖ}) S], Step ϖ → (∀ (z : S) (m d : ℕ), 0 < d → ϖ ^ (m * d) ∣ z ^ d → ϖ ^ m ∣ z) → Aic (S := S) := by
  first | exact @GlobalTheory.CompanionTheory.AicLimit.aic_of_step | exact GlobalTheory.CompanionTheory.AicLimit.aic_of_step | (intros; apply GlobalTheory.CompanionTheory.AicLimit.aic_of_step <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.integral_localization_away_in_ring : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ nonZeroDivisors S → Val ϖ → ∀ x : Localization.Away ϖ, IsIntegral S x → ∃ y : S, algebraMap S (Localization.Away ϖ) y = x := by
  first | exact @GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | exact GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral | (intros; apply GlobalTheory.CompanionTheory.ValIntClosed.exists_eq_of_isIntegral <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.section_over_idempotent_properties : ∀ {S : Type} [CommRing S] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), SecOn f 0 ∧ (∀ e e' : S, SecOn f e → SecOn f (e * e')) ∧ (SecOn f 1 → ∃ s : Spec (CommRingCat.of S) ⟶ Y, s ≫ f = 𝟙 _) := by
  first | exact @GlobalTheory.CompanionTheory.SecRules.main | exact GlobalTheory.CompanionTheory.SecRules.main | (intros; apply GlobalTheory.CompanionTheory.SecRules.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem exists_dividedPowers_map_quotient {S : Type} [CommRing S] (hS : TF (S := S)) (I J : Ideal S)
    (hI : PdI I)
    (hJ : ∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) :
    ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  obtain ⟨δ₀, -, hδ₀⟩ := exists_dividedPowers hS I hI
  have hsub : DividedPowers.IsSubDPIdeal δ₀ (J ⊓ I) :=
    { isSubideal := inf_le_right
      dpow_mem := fun n hn j hj =>
        ⟨hJ j hj.2 hj.1 n hn _ (δ₀.factorial_mul_dpow_eq_pow hj.2),
          δ₀.dpow_mem hn hj.2⟩ }
  refine ⟨DividedPowers.Quotient.dividedPowers δ₀ hsub, rfl, fun k x y hx e => ?_⟩
  rw [DividedPowers.Quotient.dpow_apply δ₀ hsub hx]
  exact congrArg _ (hδ₀ k x y hx e)

end GlobalTheory.CompanionTheory.PdTF
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.surjective_preserves_closedness_comparability : ∀ {S : Type} [CommRing S] {T : Type} [CommRing T] (φ : S →+* T), Function.Surjective φ → (Aic (S := S) → Aic (S := T)) ∧ (Val0 (S := S) → Val0 (S := T)) := by
  first | exact @GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | exact GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective | (intros; apply GlobalTheory.CompanionTheory.SurjPass.absolutely_closed_comparable_surjective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.valuation_power_iff : ∀ {S : Type} [CommRing S] (ϖ : S) (k : ℕ), k ≠ 0 → (Val (ϖ ^ k) ↔ Val ϖ) ∧ (IsAdicComplete (Ideal.span {ϖ ^ k}) S → IsAdicComplete (Ideal.span {ϖ}) S) := by
  first | exact @GlobalTheory.CompanionTheory.PowComp.val_pow | exact GlobalTheory.CompanionTheory.PowComp.val_pow | (intros; apply GlobalTheory.CompanionTheory.PowComp.val_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompMod

theorem exists_eq_add_of_mem_span_quot {S : Type} [CommRing S] (ϖ x y : S)
    (h : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) x ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) y}) :
    ∃ c d : S, x = y * c + ϖ ^ 2 * d := by
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.1 h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul] at hc'
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc')
  exact ⟨c, d, by linear_combination hd⟩

theorem mem_span_or_mem_span {S : Type} [CommRing S] (ϖ : S)
    [IsAdicComplete (Ideal.span {ϖ}) S] (h0 : Val0 (S := S ⧸ Ideal.span {ϖ ^ 2}))
    (P : Ideal S) (hP : P.IsPrime) (f g : S ⧸ compI P) :
    f ∈ Ideal.span {g, Ideal.Quotient.mk (compI P) ϖ ^ 2} ∨
      g ∈ Ideal.span {f, Ideal.Quotient.mk (compI P) ϖ ^ 2} := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective g
  obtain ⟨ε, hε, h1, h2⟩ := h0 (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)
  obtain ⟨e, ⟨he, rfl⟩, -⟩ :=
    IdemLift.existsUnique_idempotent_lift ϖ 2 two_ne_zero ε hε
  rw [← map_mul] at h1
  have h2' : Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) ((1 - e) * b) ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) a} := by
    simpa [map_mul, map_sub, map_one] using h2
  obtain ⟨c, d, hcd⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h1
  obtain ⟨c', d', hcd'⟩ := exists_eq_add_of_mem_span_quot ϖ _ _ h2'
  have key : ∀ t : S, IsIdempotentElem t → t ∈ P →
      Ideal.Quotient.mk (compI P) t = 0 := fun t ht htP =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨ht, htP⟩)
  by_cases heP : e ∈ P
  · right
    have hz := key e he heP
    have hb := congrArg (Ideal.Quotient.mk (compI P)) hcd'
    simp only [map_mul, map_add (f := _), map_sub, map_one, map_pow, hz, sub_zero, one_mul] at hb
    rw [hb]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c', Ideal.Quotient.mk _ d', by ring⟩
  · left
    have hmul : e * (1 - e) ∈ P := by
      have : e * (1 - e) = 0 := by
        have he' : e * e = e := he
        linear_combination -he'
      rw [this]
      exact P.zero_mem
    have h1e : 1 - e ∈ P := (hP.mem_or_mem hmul).resolve_left heP
    have hz := key (1 - e) he.one_sub h1e
    have hz' : Ideal.Quotient.mk (compI P) e = 1 := by
      rw [map_sub, map_one] at hz
      exact (sub_eq_zero.1 hz).symm
    have ha := congrArg (Ideal.Quotient.mk (compI P)) hcd
    simp only [map_mul, map_add (f := _), map_pow, hz', one_mul] at ha
    rw [ha]
    exact Ideal.mem_span_pair.2 ⟨Ideal.Quotient.mk _ c, Ideal.Quotient.mk _ d, by ring⟩

end GlobalTheory.CompanionTheory.CompMod
end
