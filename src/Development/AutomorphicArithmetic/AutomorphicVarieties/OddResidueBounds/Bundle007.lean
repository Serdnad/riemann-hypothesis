module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsPadicIntLiftOfIntegralAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem near_level (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N]
    (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N) (ho : Odd a) (hl : l ∣ N) (r m : ℕ)
    (hm : r + ck l (e + 1) + 1 ≤ m) (M : ℕ) [NeZero M] (h : N ∣ M) (hM : M = N * l ^ m) (g : Γ) :
    InPow l r ((yEl (e + 1) a ha φ).coeff g - (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℚ)) := by
  have haN : a.Coprime l := Nat.Coprime.coprime_dvd_right hl ha
  have haM : a.Coprime M := by
    rw [hM]
    exact Nat.Coprime.mul_right ha (Nat.Coprime.pow_right m haN)
  have hdiv : l ^ (r + ck l (e + 1) + 1) ∣ M := by
    rw [hM]
    exact Dvd.dvd.mul_left (pow_dvd_pow l hm) N
  have hI := yNear l Γ M (φ.comp (ZMod.unitsMap h)) e a r haM ho hdiv
  rw [yLevel l Γ N φ (e + 1) a ha (by omega) hl m M h haM hM] at hI
  have := (intAt_iff l r _).mp hI g
  simpa [coeff_coefMap] using this

theorem UpperTheory.V.Odd.congr :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Odd a → l ∣ N → ∃ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) ∧ ∀ r : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ (M : ℕ) [NeZero M] (h : N ∣ M), M = N * l ^ m → ∃ w : MonoidAlgebra ℤ_[l] Γ, coefMap ℤ_[l] Γ (ytEl e a (φ.comp (ZMod.unitsMap h))) = z + (l : ℤ_[l]) ^ r • w := by
  intro l _ Γ _ _ N _ φ e a ha ho hl
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set y := yEl (e + 1) a ha φ with hy
  have hy0 : IntAt l 0 y := by
    rw [intAt_iff]
    intro g
    haveI : NeZero (N * l ^ (ck l (e + 1) + 1)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl0)⟩
    have hn := near_level l Γ N φ e a ha ho hl 0 (ck l (e + 1) + 1) (by omega)
      (N * l ^ (ck l (e + 1) + 1)) (dvd_mul_right _ _) rfl g
    have h1 := hn.mem
    have h2 := add_mem h1 (intCast_mem (Zl l) ((ytEl e a (φ.comp (ZMod.unitsMap
      (dvd_mul_right N (l ^ (ck l (e + 1) + 1)))))).coeff g))
    rw [sub_add_cancel] at h2
    show y.coeff g / (l : ℚ) ^ 0 ∈ Zl l
    simpa using h2
  obtain ⟨Yp, hYp⟩ := exists_padicInt_lift_of_integralAt l y hy0
  have hYg : ∀ g, ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) = ((y.coeff g : ℚ) : ℚ_[l]) := by
    intro g
    have := congrArg (fun x => x.coeff g) hYp
    simpa using this
  refine ⟨Yp, hYg, ?_⟩
  intro r
  refine ⟨r + ck l (e + 1) + 1, ?_⟩
  intro m hm M _ h hM
  have hc : ∀ g, ∃ c : ℤ_[l], (((ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g : ℤ) : ℤ_[l]) =
      Yp.coeff g + (l : ℤ_[l]) ^ r * c := by
    intro g
    have hn := near_level l Γ N φ e a ha ho hl r m hm M h hM g
    set t : ℤ := (ytEl e a (φ.comp (ZMod.unitsMap h))).coeff g
    set q : ℚ := (y.coeff g - (t : ℚ)) / (l : ℚ) ^ r with hqdef
    have hq : ‖(q : ℚ_[l])‖ ≤ 1 := Padic.norm_rat_le_one (mem_Zl.mp hn)
    have hqr : q * (l : ℚ) ^ r = y.coeff g - t := by
      rw [hqdef]
      exact div_mul_cancel₀ _ (pow_ne_zero _ (by exact_mod_cast hl0))
    have hqr' : (q : ℚ_[l]) * (l : ℚ_[l]) ^ r = ((y.coeff g : ℚ) : ℚ_[l]) - (t : ℚ_[l]) := by
      have := congrArg (fun x : ℚ => (x : ℚ_[l])) hqr
      push_cast at this
      exact this
    let c : ℤ_[l] := ⟨(q : ℚ_[l]), hq⟩
    refine ⟨-c, ?_⟩
    apply Subtype.ext
    show (t : ℚ_[l]) = ((Yp.coeff g : ℤ_[l]) : ℚ_[l]) + (l : ℚ_[l]) ^ r * -(q : ℚ_[l])
    rw [hYg g]
    linear_combination hqr'
  choose c hc using hc
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  apply MonoidAlgebra.ext
  ext g
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, coeff_coefMap, hc g]
  simp [smul_eq_mul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem int_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X.natAbs ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hn' (dvd_zero l)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
  · have hu : IsUnit ((n' : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).mp h
    rw [Int.cast_natCast] at hu
    have h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l]) :=
      map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)
    refine h1.trans ?_
    rw [he]
    push_cast
    exact hu.mul_right_dvd.mpr dvd_rfl

theorem UpperTheory.V.Odd.detVal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Function.Surjective φ → φ (-1) ≠ 1 → 1 ≤ e → 1 < a → ∀ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) ∧ detR (φ (-1)) ((-1) ^ (e + 1)) z ∣ (l : ℤ_[l]) ^ r := by
  intro l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz
  obtain ⟨X, hX0, hXb, hXe⟩ := higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ
  obtain ⟨r, hr1, hr2⟩ := int_dvd_pow l X hX0
  refine ⟨r, ?_, ?_⟩
  · have h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2) := by
      exact_mod_cast hr1.trans hXb
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    have h2 := Real.log_le_log hl0 h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    calc (r : ℝ) * Real.log l ≤ ((Nat.card Γ / 2 : ℕ) : ℝ) * Real.log (bdX N a (e + 1)) := h2
      _ ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) :=
        mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg _)
  · refine dvd_trans ?_ hr2
    have hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z =
        MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ) := by
      ext g
      have h := hz g
      simp
      exact h
    have hd := congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap
    rw [detR_map, detR_map] at hd
    have hq := congrArg (Rat.castHom ℚ_[l]) hXe
    rw [map_mul, map_pow, ← hd] at hq
    have hX'' : (X : ℤ_[l]) =
        (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z := by
      apply PadicInt.ext
      push_cast
      simp at hq
      exact hq
    rw [hX'']
    exact dvd_mul_left _ _
end
