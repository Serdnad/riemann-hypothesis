module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle781
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle782
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mul_eq_smul_one_comm {R : Type} [CommRing R] [IsDomain R] {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} {c : R} (hc : c ≠ 0) (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) R)) :
    M' * M = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc M.det • (M' * M) = (M.adjugate * M) * (M' * M) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa [Matrix.smul_apply] using mul_left_cancel₀ hdet h2

theorem eq_zero_of_mul_eq_zero_of_mul_eq_smul {R : Type} [CommRing R] {d : ℕ}
    {W W' M : Matrix (Fin d) (Fin d) R} {t : R} (ht : t ∈ nonZeroDivisors R)
    (h : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hM : W * M = 0) : M = 0 := by
  have hdet : W.det ∈ nonZeroDivisors R := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R := pow_mem ht _
    rw [mem_nonZeroDivisors_iff] at htp ⊢
    refine ⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]),
      fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩
  have key : W.det • M = 0 := by
    rw [← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢
  exact (mem_nonZeroDivisors_iff.1 hdet).1 _ h2

theorem map_smul_ringHom {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (f : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem Height.bas_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  intro l _ K bk d ρ τ s ht hτ Φ hΦ
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := by
    unfold BK.ρ₀
    exact NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hρ1 : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    apply NNReal.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · have : (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith
  have hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ
  have hXl : frobS l bk.a (X : bk.S) = X ^ l := by
    simp [frobS]
  have hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [← bk.ev_frob, hXl, map_pow]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def
  have hΦA : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius ΦA := isDiscMap_map _ _
  have hcomm : i.comp Φ = ΦA.comp i := by
    have h1 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (i.comp Φ) :=
      ⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩
    have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (ΦA.comp i) := by
      have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
        RingHom.ext bk.ev_frob
      rw [e]
      exact ⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩
    exact h1.unique h2
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective i := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi
  have hlS : (l : bk.S) ∈ nonZeroDivisors bk.S :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1
  have hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc l K bk τ hτ
  have hφE : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map i
    rw [hi.ext] at h; exact h
  have hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a := hi.ext
  have hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a) := hΦA.ext
  have hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a) := fun a => by
    simp only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]
  have hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
    mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul

  have hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M' := fun M M' h => by
    ext a b; exact hinj (congrFun (congrFun h a) b)
  apply hmapinj
  have hcomm' : ∀ z, i (Φ z) = ΦA (i z) := RingHom.congr_fun hcomm
  simp only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow,
    map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]

  set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def
  set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def
  set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def
  set XA := s.X.map bk.iS with hXA
  set X'A := s.X'.map bk.iS with hX'A
  set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA
  set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A
  set FA := s.F.map (bk.iS.comp C) with hFA
  set AA := ht.A.map bk.iS with hAA
  set Zi := ht.Z.map i with hZi
  set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ
  set YA := ht.Y.map bk.iA with hYA
  have hW : s.W * Zi = YA := ht.W_mul i hi
  have hZΦ' : ZΦ = Zi.map ΦA := by rw [hZΦ, hZi, Matrix.map_map]; rfl
  have hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA := by rw [hZΦ', ← Matrix.map_mul, hW]
  have hP : e ^ ht.a • YA.map ΦA = YA * AA := by
    have h := congrArg (fun M => M.map bk.iA) ht.φ
    simp only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h
    have e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius) := by
      rw [hYA, Matrix.map_map]; congr 1; funext x; exact hΦiA x
    rw [e1]; rw [map_pow] at h; exact h
  have hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA) := by
    have h := s.φ ΦA hΦA
    rw [Matrix.map_mul] at h
    have e1 : (s.X'.map bk.iS).map ΦA = φX'A := by
      rw [Matrix.map_map, hφX'A]; congr 1; funext x; exact hΦiS x
    rw [e1] at h
    simpa only [map_natCast, map_pow] using h
  have hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map bk.iS) s.X_mul
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA := by
    apply ((hφE.pow s.N).smul_left_cancel).1
    calc φe ^ s.N • (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA
        = (L ^ s.c₁ • (s.W.map ΦA * φX'A)) * φXA := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
          congr 1; ring
      _ = _ := by rw [hS, Matrix.smul_mul]
  have hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0 := by
    rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ,
      smul_comm, ← Matrix.smul_mul, hQ]
    simp only [Matrix.mul_assoc]
  have hD' := eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD
  rw [sub_eq_zero] at hD'
  have hX := congrArg (fun M => XA * M) hD'
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX
  have G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ)) := by
    apply ((hL.pow s.c₂).smul_left_cancel).1
    rw [smul_smul, smul_smul]
    calc (L ^ s.c₂ * (L ^ s.c₁ * φe ^ s.N)) • (XA * Zi * AA) = (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (XA * Zi * AA) := by
          congr 1; ring
      _ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring
  exact G

end GlobalTheory.BSP
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

theorem isBeta_scale {bk : BK K} (F : Frame bk N d ρ) {m k : ℕ} {β : Matrix (Fin d) (Fin d) bk.S}
    (hβ : F.IsBeta m k β) (j : ℕ) : F.IsBeta m (k + j) ((l : bk.S) ^ j • β) := by
  refine ⟨fun p q => ?_, fun g p q => ?_⟩
  · have : ((l : bk.S) ^ j • β - (l : bk.S) ^ (k + j) • (1 : Matrix (Fin d) (Fin d) bk.S)) p q =
        (l : bk.S) ^ j * (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) p q := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, pow_add]; ring
    rw [this]; exact dvd_mul_of_dvd_right (hβ.1 p q) _
  · have h2 : ((l : bk.S) ^ j • β).map bk.ev = (l : Ainf l) ^ j • β.map bk.ev := by
      ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    have h1 : (((l : bk.S) ^ j • β).map bk.ev).map (Per.σA (g : GQ l)) =
        (l : Ainf l) ^ j • (β.map bk.ev).map (Per.σA (g : GQ l)) := by
      rw [h2]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [h1, h2, Matrix.mul_smul, ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hβ.2 g p q) _

end GlobalTheory.BKLim.BetaBd


open GlobalTheory.BKLim.BetaBd in
theorem GlobalTheory.BKLim.beta_bdd_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  intro l _ K bk m
  obtain ⟨g, z, ⟨w, hw, hzw⟩, hz⟩ := GlobalTheory.T.exists_galois_elem_cyclotomic_period_not_root_of_unity l K bk
  have hu : ∀ i, 1 ≤ i → Per.θ l w ^ i - 1 ≠ 0 := by
    intro i hi h
    apply hz i hi
    have h1 : ((Per.θ l w : OC l) : ℂ_[l]) ^ i = 1 := by
      have := congrArg (fun t : OC l => (t : ℂ_[l])) (sub_eq_zero.1 h)
      simpa using this
    rw [(thetaD_props l).2.2.2.1 w] at hzw
    calc z ^ i = z ^ i * ((Per.θ l w : ℂ_[l]) ^ i) := by rw [h1, mul_one]
      _ = (z * (Per.θ l w : ℂ_[l])) ^ i := (mul_pow _ _ _).symm
      _ = 1 := by rw [hzw, one_pow]
  choose a ha using fun i : {i : ℕ // 1 ≤ i} => exists_dvd_bound _ (hu i.1 i.2)
  let A : ℕ → ℕ := fun i => if h : 1 ≤ i then a ⟨i, h⟩ else 0
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, A j
  have hSs : ∀ i, S (i + 1) = S i + A i := fun i => Finset.sum_range_succ _ _
  have hSm : ∀ i j, i ≤ j → S i ≤ S j := fun i j h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  refine ⟨S m, fun N d ρ F k β hβ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨(l : bk.S) ^ S 0 • 1, fun p q => by simp, fun g p q => by simp⟩
  by_cases hk : k < S m
  · refine ⟨(l : bk.S) ^ (S m - k) • β, ?_⟩
    have := isBeta_scale F hβ (S m - k)
    rwa [Nat.add_sub_cancel' hk.le] at this
  push_neg at hk
  have key : ∀ i, 1 ≤ i → i ≤ m → ∃ γ : Matrix (Fin d) (Fin d) bk.S,
      ∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ (k - S i) • γ) p q := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ him
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨(l : bk.S) ^ S 1 • 1, fun p q => ?_⟩
        have hS : S 1 ≤ k := le_trans (hSm 1 m him) hk
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hS, pow_one]
        exact hβ.1 p q
      · obtain ⟨γ, hγ⟩ := ih hi0 (by omega)
        obtain ⟨δ, hδ1, hδ2⟩ := GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem l K bk N d ρ F g w hw m k β hβ i (k - S i) him γ hγ
        have hAi : A i = a ⟨i, hi0⟩ := dif_pos hi0
        have hS1 : S (i + 1) ≤ k := le_trans (hSm _ _ him) hk
        have hle : a ⟨i, hi0⟩ ≤ k - S i := by rw [hSs] at hS1; omega
        have hexp : k - S i - a ⟨i, hi0⟩ = k - S (i + 1) := by rw [hSs, hAi]; omega
        have hlift : ∀ p q, ∃ s' t : bk.S, δ p q = (l : bk.S) ^ (k - S (i + 1)) * s' + bk.E * t := by
          intro p q
          obtain ⟨y, hy⟩ := hδ2 p q
          obtain ⟨y', hy'⟩ := ha ⟨i, hi0⟩ _ y _ hy hle
          rw [hexp] at hy'
          exact GlobalTheory.T.exists_primePow_dvd_mod_eisenstein_of_theta l K bk _ _ y' hy'
        choose δ' t ht using hlift
        refine ⟨(l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ', fun p q => ?_⟩
        have hpow : (l : bk.S) ^ (k - S (i + 1)) * (l : bk.S) ^ A i = (l : bk.S) ^ (k - S i) := by
          rw [← pow_add]; congr 1; rw [hSs] at hS1 ⊢; omega
        have e : (β - (l : bk.S) ^ (k - S (i + 1)) • ((l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ')) p q =
            (β - (l : bk.S) ^ (k - S i) • γ - bk.E ^ i • δ) p q + bk.E ^ (i + 1) * t p q := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
          linear_combination (bk.E ^ i) * ht p q - γ p q * hpow
        rw [e]
        exact dvd_add (hδ1 p q) (dvd_mul_right _ _)
  obtain ⟨γ, hγ⟩ := key m hm le_rfl
  refine ⟨γ, ?_⟩
  have := GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul l K bk N d ρ F m k (k - S m) β γ hβ hm (Nat.sub_le k (S m)) hγ
  rwa [Nat.sub_sub_self hk] at this

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.EtBasis

theorem zW_dvd {l : ℕ} [Fact l.Prime] {n : ℕ} {x : ℤ_[l]} (h : (l : ℤ_[l]) ^ n ∣ x) :
    (l : WCb l) ^ n ∣ algebraMap ℤ_[l] (WCb l) x := by
  simpa [map_pow, map_natCast] using map_dvd (algebraMap ℤ_[l] (WCb l)) h

theorem flatKer {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) (hu : ∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) : ∃ w, u = zW f *ᵥ w := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] (WCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective
  choose y hy using hu
  let x : ((Fin d' ⊕ Fin d) → ℤ_[l]) →ₗ[ℤ_[l]] WCb l := Fintype.linearCombination ℤ_[l] (Sum.elim u y)
  let B : Matrix (Fin d' ⊕ Fin d) (Fin d) ℤ_[l] :=
    Matrix.fromRows Piᵀ (Matrix.diagonal fun _ => -((l : ℤ_[l]) ^ n))
  let F : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] ((Fin d' ⊕ Fin d) → ℤ_[l]) := Matrix.toLin' B
  have hxF : x ∘ₗ F = 0 := by
    ext i : 2
    have := hy i
    simp [x, F, B, Fintype.linearCombination_apply, Fintype.sum_sum_type, Matrix.mulVec, dotProduct,
      Algebra.smul_def, Matrix.diagonal_apply] at this ⊢
    rw [this]
    simp [apply_ite (algebraMap ℤ_[l] (WCb l)), ite_mul]
  obtain ⟨k, a, yy, hx, haF⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxF
  let A : Fin k → (Fin d' ⊕ Fin d) → ℤ_[l] := fun m p => a (fun q => if p = q then 1 else 0) m
  have hyy : ∀ v : Fin k →₀ ℤ_[l], yy v = ∑ m, v m • yy (Finsupp.single m 1) := by
    intro v
    have : yy = Finsupp.linearCombination ℤ_[l] (fun m => yy (Finsupp.single m 1)) := by
      refine Finsupp.lhom_ext fun m r => ?_
      rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
    conv_lhs => rw [this]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp
  have hA : ∀ m i, (Pi *ᵥ fun j => A m (Sum.inl j)) i = (l : ℤ_[l]) ^ n * A m (Sum.inr i) := by
    intro m i
    have h0 := congrArg (fun v => v m) (LinearMap.congr_fun haF (_root_.Pi.single i 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0
    rw [LinearMap.pi_apply_eq_sum_univ] at h0
    simp [A, F, B, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, _root_.Pi.single_apply] at h0 ⊢
    linear_combination h0
  have hu' : ∀ j, u j = ∑ m, A m (Sum.inl j) • yy (Finsupp.single m 1) := by
    intro j
    have h1 : u j = x (fun q => if Sum.inl j = q then 1 else 0) := by
      simp [x, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    rw [h1, hx, LinearMap.comp_apply, hyy]
  choose w hw using fun m => (hker (fun j => A m (Sum.inl j))).1 (fun i => ⟨A m (Sum.inr i), hA m i⟩)
  refine ⟨fun t => ∑ m, w m t • yy (Finsupp.single m 1), funext fun j => ?_⟩
  rw [hu' j]
  have h2 : ∀ m, A m (Sum.inl j) = ∑ t, f j t * w m t := fun m => congrFun (hw m) j

  simp only [h2, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def, Matrix.map_apply,
  map_sum, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem kerW {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) : (∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) ↔ ∃ w, u = zW f *ᵥ w := by
  refine ⟨flatKer Pi f hker u, ?_⟩
  rintro ⟨w, rfl⟩ i
  have hPf : ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * f) i j := by
    intro i j
    have := (hker (f *ᵥ _root_.Pi.single j 1)).2 ⟨_, rfl⟩ i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, _root_.Pi.single_apply] using this
  have hm : zW Pi * zW f = zW (Pi * f) := (Matrix.map_mul).symm
  rw [Matrix.mulVec_mulVec, hm]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (zW_dvd (hPf i j)) _

end GlobalTheory.BKLim.EtBasis


open GlobalTheory.BKLim.EtBasis in
theorem GlobalTheory.BKLim.etBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F' Pi hn hOnto
  obtain ⟨f, ρ'', hdet, hfeq, hker⟩ := GlobalTheory.T.exists_kernel_lattice_equivariant_modPow l (↥(GK K)) d d' n ρ ρ' Pi hOnto
  obtain ⟨T'', P, hT'', hP, hfT⟩ := GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice l K bk τ hτ N d' (fun g => (ρ' g).val)
    (fun g => (ρ'' g).val) F' f hdet (fun g => (ρ'' g).isUnit) hfeq
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 F'.unit
  have hT''d := (Matrix.isUnit_iff_isUnit_det _).1 hT''
  apply GlobalTheory.T.exists_smith_factorization_etale_OE_mod_prime_pow l K bk d d' n (zW Pi * F'.T) P hn hP
  · obtain ⟨S, hS⟩ := hOnto.surj
    refine ⟨F'.T⁻¹ * zW S, fun i j => ?_⟩
    have : zW Pi * F'.T * (F'.T⁻¹ * zW S) - 1 = zW (Pi * S - 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F'.T, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
      show _ = (algebraMap ℤ_[l] (WCb l)).mapMatrix (Pi * S - 1)
      rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul]
    rw [this]
    exact zW_dvd (hS i j)
  · intro v
    rw [← Matrix.mulVec_mulVec, kerW Pi f hker]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨T''⁻¹ *ᵥ w, ?_⟩
      have h1 : zW f = F'.T * P * T''⁻¹ := by
        rw [← hfT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT''d, Matrix.mul_one]
      calc v = F'.T⁻¹ *ᵥ (F'.T *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mulVec]
        _ = P *ᵥ (T''⁻¹ *ᵥ w) := by
            rw [hw, h1]
            simp only [Matrix.mulVec_mulVec]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
    · rintro ⟨w, rfl⟩
      exact ⟨T'' *ᵥ w, by simp only [Matrix.mulVec_mulVec, hfT]⟩
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.twisted_matrix_congruence_lift_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  first | (exact @GlobalTheory.BKLim.limit_basis_link_mod) | (exact GlobalTheory.BKLim.limit_basis_link_mod) | (intros; apply GlobalTheory.BKLim.limit_basis_link_mod  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  first | (exact @GlobalTheory.BKLim.GalStab.galois_stable) | (exact GlobalTheory.BKLim.GalStab.galois_stable) | (intros; apply GlobalTheory.BKLim.GalStab.galois_stable  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  first | exact @GlobalTheory.RallisCusp.nonGraph_sum_eq_zero | exact GlobalTheory.RallisCusp.nonGraph_sum_eq_zero | (intros; apply GlobalTheory.RallisCusp.nonGraph_sum_eq_zero <;> assumption)
end
