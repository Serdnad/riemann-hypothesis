module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle634
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle761
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle731
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle760
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle756
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle757
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle759
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.GalD

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {c : R} (hc : c ∈ nonZeroDivisors R)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 h1

theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem mul_eq_smul_comm {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    {X X' : Matrix n n R} {c : R} (hc : c ∈ nonZeroDivisors R) (h : X * X' = c • (1 : Matrix n n R)) :
    X' * X = c • (1 : Matrix n n R) := by
  have hdet : X.det ∈ nonZeroDivisors R := by
    have h4 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    have h5 : X.det * X'.det ∈ nonZeroDivisors R := h4 ▸ pow_mem hc _
    exact (mul_mem_nonZeroDivisors.1 h5).1
  have h2 : X * (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one,
      sub_self]
  have h3 : X.det • (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [← Matrix.one_mul (X' * X - c • (1 : Matrix n n R)), ← smul_mul_assoc, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h2, Matrix.mul_zero]
  rw [← smul_zero X.det] at h3
  exact sub_eq_zero.1 (smul_cancel hdet h3)

theorem key {R : Type} [CommRing R] {n : Type} [Fintype n] {P YG Ya U UG Bi Bg ε : Matrix n n R}
    {L e ge t gt : R} {N : ℕ} (hc : L * ge ^ (2 * N) * e ^ (2 * N) ∈ nonZeroDivisors R)
    (hY : U * Bi = (L * e ^ (2 * N)) • Ya) (hYG : UG * Bg = (L * ge ^ (2 * N)) • YG)
    (hgal : (e * t) ^ N • (P * UG) = (ge * gt) ^ N • U) (hR : ge ^ N • (Bi * ε) = e ^ N • Bg) :
    t ^ N • (P * YG) = gt ^ N • (Ya * ε) := by
  refine smul_cancel hc ?_
  calc (L * ge ^ (2 * N) * e ^ (2 * N)) • (t ^ N • (P * YG))
      = (e ^ N * (e * t) ^ N) • (P * ((L * ge ^ (2 * N)) • YG)) := by
        rw [smul_smul, mul_smul_comm, smul_smul]; congr 1; ring
    _ = (e ^ N * (e * t) ^ N) • (P * (UG * Bg)) := by rw [hYG]
    _ = e ^ N • (((e * t) ^ N • (P * UG)) * Bg) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]
    _ = e ^ N • (((ge * gt) ^ N • U) * Bg) := by rw [hgal]
    _ = (ge * gt) ^ N • (U * (e ^ N • Bg)) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm]
    _ = (ge * gt) ^ N • (U * (ge ^ N • (Bi * ε))) := by rw [hR]
    _ = ((ge * gt) ^ N * ge ^ N) • ((U * Bi) * ε) := by rw [mul_smul_comm, smul_smul, Matrix.mul_assoc]
    _ = ((ge * gt) ^ N * ge ^ N) • (((L * e ^ (2 * N)) • Ya) * ε) := by rw [hY]
    _ = (L * ge ^ (2 * N) * e ^ (2 * N)) • (gt ^ N • (Ya * ε)) := by
        rw [smul_mul_assoc, smul_smul, smul_smul]; congr 1; ring

end GlobalTheory.BSP.GalD


open GlobalTheory.BSP.GalD in
theorem GlobalTheory.BSP.Height.rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  intro l _ K bk d ρ τ s ht _hτ g ε hrel
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := NNReal.rpow_pos hl0
  have h0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  have h1 : ‖toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).1
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev h0 with hi_def
  set G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (Per.σA (g : GQ l)) h1 with hG_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  have hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G := isDiscMap_map _ _
  have hFg : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf ((ainfHom K g).comp bk.ι)) (G.comp i) :=
    ⟨fun a => by
      change G (i (toDisc l X bk.ρ₀ a)) = toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev a))
      rw [hi.ext, hG.ext], fun x => (hG.norm_le _).trans (hi.norm_le x)⟩
  have hR : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ s.N • (ht.bas.map i * ε) =
      bk.iA (bk.ev bk.E) ^ s.N • ht.bas.map (G.comp i) := hrel i (G.comp i) hi hFg
  have hGA : ∀ a, G (bk.iA a) = bk.iA (Per.σA (g : GQ l) a) := hG.ext

  have hbi : ht.bas.map i = s.X.map bk.iS * ht.Z.map i := by
    rw [Height.bas, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  have hbg : ht.bas.map (G.comp i) = (s.X.map bk.iS).map G * (ht.Z.map i).map G := by
    rw [← Matrix.map_mul, ← hbi, Matrix.map_map]; rfl

  obtain ⟨ιb, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have he : bk.iA (bk.ev bk.E) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ιb tb).2.1
  have hL : ((l : bk.DA bk.ρ₀) ^ s.c₂) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow _).mem_nonZeroDivisors
  obtain ⟨w, hw⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).2.1
  have hw' : bk.ev bk.E * (show Ainf l from (w : (ainfObj K).A)) = Per.σA (g : GQ l) (bk.ev bk.E) := hw
  have hwu : IsUnit (bk.iA (show Ainf l from (w : (ainfObj K).A))) := w.isUnit.map bk.iA
  have hge : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
    rw [← hw', map_mul]
    exact mul_mem he hwu.mem_nonZeroDivisors

  have hXX1 : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hXX := mul_eq_smul_comm (mul_mem hL (pow_mem he _)) hXX1
  set U := s.W * s.X'.map bk.iS with hU
  have hY : U * (s.X.map bk.iS * ht.Z.map i) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (bk.ev bk.E) ^ (2 * s.N)) • ht.Y.map bk.iA := by
    rw [hU, Matrix.mul_assoc, ← Matrix.mul_assoc (s.X'.map bk.iS), hXX, smul_mul_assoc, Matrix.one_mul,
      mul_smul_comm, ht.W_mul i hi]
  have hYG : U.map G * ((s.X.map bk.iS).map G * (ht.Z.map i).map G) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ (2 * s.N)) •
        (ht.Y.map bk.iA).map G := by
    have := congrArg (fun M => Matrix.map M G) hY
    simp only [Matrix.map_mul, map_smul_hom] at this
    rw [this, map_mul, map_pow, map_pow, map_natCast, hGA]
  have hgal := s.gal g G hG
  rw [← hU, map_mul, map_mul] at hgal
  have hgoal : (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) =
      (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (ht.Y.map bk.iA).map G := by
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
    congr 1
    ext a b
    exact (hGA _).symm
  rw [hgoal]
  rw [hbg] at hR
  rw [hbi] at hR
  simp only [map_mul] at hgal
  exact key (mul_mem (mul_mem hL (pow_mem hge _)) (pow_mem he _)) hY hYG hgal hR
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {m n : Type*} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pre_of_etale : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (T A0 A0' : Matrix (Fin d) (Fin d) (WCb l)) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit T → (∀ i j, A0 i j ∈ bk.OE) → (∀ i j, A0' i j ∈ bk.OE) → T.map (frobW l) = T * A0 → A0 * A0' = 1 → (∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T) → Y.map (inclW l) = inclW l τ ^ N • T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → ∃ F : Pre bk N d ρ, F.T = T := by
  intro l _ K bk τ hτ N d ρ T A0 A0' Y Y' hT hA0 hA0' hφ hA hfix hY hYY'
  classical
  have htu : IsUnit (inclW l τ) := (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1
  obtain ⟨-, hinj, -⟩ := GlobalTheory.BSP.BK.evW_isUnit_injective_dvd l K bk
  have hdet : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hT
  have hTi : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hdet
  have hiT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hdet
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  have hYm : Y.map (inclW l) = t ^ N • T := hY
  have hYY'm : Y.map (inclW l) * Y'.map (inclW l) = t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, hYY', map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  have hTY' : T * Y'.map (inclW l) = t ^ N • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [hYm, Matrix.smul_mul, show 2 * N = N + N by ring, pow_add, ← smul_smul] at hYY'm
    exact ((htu.pow N).smul_left_cancel).1 hYY'm
  have hY'm : Y'.map (inclW l) = t ^ N • T⁻¹ := by
    calc Y'.map (inclW l) = T⁻¹ * (T * Y'.map (inclW l)) := by rw [← Matrix.mul_assoc, hTi, Matrix.one_mul]
      _ = t ^ N • T⁻¹ := by rw [hTY', Matrix.mul_smul, Matrix.mul_one]
  have hfr : ∀ M : Matrix (Fin d) (Fin d) (Ainf l),
      (M.map WittVector.frobenius).map (inclW l) = (M.map (inclW l)).map (frobW l) := by
    intro M; ext i j; simp [GlobalTheory.Prism.frobW_inclW]
  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hfmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have hfsmul : ∀ (c : WCb l) (M : Matrix (Fin d) (Fin d) (WCb l)), (c • M).map (frobW l) = frobW l c • M.map (frobW l) :=
    fun c M => map_smul_ringHom (frobW l).toRingHom c M

  have hOE : ∀ s : bk.S, bk.evW s ∈ bk.OE := fun s n => ⟨0, s, 0, by simp⟩
  obtain ⟨A, hAm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0) (Y' * Y.map WittVector.frobenius)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0 i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, hφ, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hTi,
        Matrix.one_mul, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0) (by ring))
  have hTf : (T⁻¹).map (frobW l) * T = A0' := by
    have h1 : (T⁻¹).map (frobW l) * T.map (frobW l) = 1 := by
      rw [← hfmul, hTi, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hφ, ← Matrix.mul_assoc] at h1
    calc (T⁻¹).map (frobW l) * T = (T⁻¹).map (frobW l) * T * (A0 * A0') := by rw [hA, Matrix.mul_one]
      _ = A0' := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  obtain ⟨A', hA'm⟩ := GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d (2 * N) (e ^ N • A0') (Y'.map WittVector.frobenius * Y)
    (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact bk.OE.mul_mem (bk.OE.pow_mem (hOE _) _) (hA0' i j)) (by
      rw [Matrix.map_mul, hfr, hY'm, hYm, hfsmul, map_pow, hft, Matrix.smul_mul, Matrix.mul_smul, hTf, smul_smul, smul_smul]
      rw [← ht]; exact congrArg (· • A0') (by ring))
  refine ⟨{ T := T, unit := hT, A := A, A' := A', A_mul := ?_, φ := ?_, fix := hfix }, rfl⟩
  · refine Matrix.map_injective hinj (?_ : (A * A').map bk.evW = (bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.evW)
    rw [Matrix.map_mul, hAm, hA'm, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mul,
      Matrix.mul_smul, hA, smul_smul, map_pow, ← pow_add]
    rw [← he, two_mul]
  · rw [hAm, hφ, Matrix.mul_smul]

end GlobalTheory.BKLim

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) → ∀ g : ↥(GK K), (F.ε g).map ((aDp l).comp WittVector.frobenius) * B.map (Per.σDp (g : GQ l)) = B := by
  first | exact @GlobalTheory.BKLim.BinfInv.inv | exact GlobalTheory.BKLim.BinfInv.inv | (intros; apply GlobalTheory.BKLim.BinfInv.inv <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriod_frobenius_rational_over_kisinRing : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Z1 : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y1.det ≠ 0 → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z1.map j = Y1.map bk.iA) → ∃ (δ : bk.S) (A1 : Matrix (Fin d) (Fin d) (bk.S)), δ ≠ 0 ∧ bk.ev δ • Y1.map WittVector.frobenius = Y1 * A1.map bk.ev := by
  first | (exact @GlobalTheory.BKLim.FrobRational.main) | (exact GlobalTheory.BKLim.FrobRational.main) | (intros; apply GlobalTheory.BKLim.FrobRational.main  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriod_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BKLim.wseed_span_frobenius_stable | exact GlobalTheory.BKLim.wseed_span_frobenius_stable | (intros; apply GlobalTheory.BKLim.wseed_span_frobenius_stable; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_finiteProjective_descent_prismCover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∃ (P : Type) (_ : AddCommGroup P) (_ : Module B.A P) (_ : Module.Finite B.A P) (_ : Module.Projective B.A P) (u : P →ₛₗ[h.f] (Fin d → C.A)), SemiBC u ∧ ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i) := by
  first | exact @GlobalTheory.BSP.CoverDesc.exists_descent | exact GlobalTheory.BSP.CoverDesc.exists_descent | (intros; apply GlobalTheory.BSP.CoverDesc.exists_descent <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.limitVector_mem_OE_and_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, R n i j ∈ bk.OE) → (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → ∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v) := by
  first | (exact @GlobalTheory.BKLim.limvec_mem) | (exact GlobalTheory.BKLim.limvec_mem) | (intros; apply GlobalTheory.BKLim.limvec_mem  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistable_disc_period_basis_isUnit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W * Z.map j = Y.map bk.iA) → IsUnit Z := by
  first | exact @GlobalTheory.BKLim.wseed_Z_isUnit | exact GlobalTheory.BKLim.wseed_Z_isUnit | (intros; apply GlobalTheory.BKLim.wseed_Z_isUnit; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal


theorem _root_.GlobalTheory.T.semistablePeriod_frameCocycle_frobenius_twist_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (Ψ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀) (V : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (ε : Matrix (Fin d) (Fin d) (Ainf l)), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Ψ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ → G (bk.iS bk.E) ^ s.N • (V.map i * ε.map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (V.map i).map G) → G (bk.iS (frobS l bk.a bk.E)) ^ s.N • ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i * (ε.map WittVector.frobenius).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ s.N • (s.κ g * ((s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * V.map Ψ).map i).map G) := by
  first | (exact @GlobalTheory.BKLim.FrobTwistKappa.main) | (exact GlobalTheory.BKLim.FrobTwistKappa.main) | (intros; apply GlobalTheory.BKLim.FrobTwistKappa.main  <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.semistablePeriod_frobenius_of_scaled_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BKLim.wseed_frob_inverse | exact GlobalTheory.BKLim.wseed_frob_inverse | (intros; apply GlobalTheory.BKLim.wseed_frob_inverse; all_goals assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

theorem GlobalTheory.BKLim.BetaDiv.isBeta_div : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (m k n : ℕ) (β γ : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → 1 ≤ m → n ≤ k → (∀ p q, bk.E ^ m ∣ (β - (l : bk.S) ^ n • γ) p q) → F.IsBeta m (k - n) γ := by
  intro l _ K bk N d ρ F m k n β γ hβ hm hnk hd
  have hT := GlobalTheory.T.eisensteinImage_pow_ideal_ainf_properties l K bk
  have strip : ∀ (r n : ℕ) (a : Ainf l), bk.ev bk.E ^ r ∣ (l : Ainf l) ^ n * a → bk.ev bk.E ^ r ∣ a := by
    intro r n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      refine ih a ((hT r).1 _ ?_)
      rw [pow_succ', mul_assoc] at h
      exact h
  have hk : (l : bk.S) ^ k = (l : bk.S) ^ n * (l : bk.S) ^ (k - n) := by
    rw [← pow_add, Nat.add_sub_cancel' hnk]
  refine ⟨fun i j => ?_, fun g i j => ?_⟩
  · have h1 := hβ.1 i j
    have h2 : bk.E ∣ (β - (l : bk.S) ^ n • γ) i j := (dvd_pow_self _ (by omega : m ≠ 0)).trans (hd i j)
    have h3 : bk.E ∣ (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j := by
      have : (l : bk.S) ^ n * (γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j =
          (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) i j - (β - (l : bk.S) ^ n • γ) i j := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hk]
        ring
      rw [this]
      exact dvd_sub h1 h2
    obtain ⟨c, hc⟩ := h3
    have h4 : bk.ev bk.E ^ 1 ∣ (l : Ainf l) ^ n * bk.ev ((γ - (l : bk.S) ^ (k - n) • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) :=
      ⟨bk.ev c, by rw [pow_one, ← map_mul, ← hc, map_mul, map_pow, map_natCast]⟩
    simpa using (hT 1).2.1 _ (strip 1 n _ h4)
  · set Φ := (F.ε g).map WittVector.frobenius with hΦ
    set σ := Per.σA (g : GQ l) with hσ
    set δ := β - (l : bk.S) ^ n • γ with hδ
    have hev : ∀ p q, bk.ev bk.E ^ m ∣ (δ.map bk.ev) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      exact ⟨bk.ev c, by rw [Matrix.map_apply, hc, map_mul, map_pow]⟩
    have hσE : bk.ev bk.E ∣ σ (bk.ev bk.E) := by
      have := GlobalTheory.BKLim.BetaBd.dvd_σA_ev_sub bk g bk.E
      simpa using dvd_add this (dvd_refl (bk.ev bk.E))
    have hevσ : ∀ p q, bk.ev bk.E ^ m ∣ ((δ.map bk.ev).map σ) p q := fun p q => by
      obtain ⟨c, hc⟩ := hd p q
      rw [Matrix.map_apply, Matrix.map_apply, hc, map_mul, map_mul, map_pow, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hσE m) _
    have hβeq : β = (l : bk.S) ^ n • γ + δ := by rw [hδ]; abel
    have hmap : (β.map bk.ev) = (l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev := by
      rw [hβeq]; ext p q; simp
    have hmapσ : (β.map bk.ev).map σ = (l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ := by
      rw [hmap]; ext p q; simp
    have hD := hβ.2 g i j
    rw [hmapσ, hmap] at hD
    have hsplit : (Φ * ((l : Ainf l) ^ n • (γ.map bk.ev).map σ + (δ.map bk.ev).map σ) -
        ((l : Ainf l) ^ n • γ.map bk.ev + δ.map bk.ev)) i j =
        (l : Ainf l) ^ n * (Φ * (γ.map bk.ev).map σ - γ.map bk.ev) i j +
          ((Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [hsplit] at hD
    have hrest : bk.ev bk.E ^ m ∣ (Φ * (δ.map bk.ev).map σ) i j - (δ.map bk.ev) i j := by
      refine dvd_sub ?_ (hev i j)
      rw [Matrix.mul_apply]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hevσ k j) _
    exact strip m n _ ((dvd_add_left hrest).1 hD)

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.theta_conj_bounded_compatible_breuilKisin_frames : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  first | exact @GlobalTheory.HTBound.bounded_compat | exact GlobalTheory.HTBound.bounded_compat | (intros; apply GlobalTheory.HTBound.bounded_compat; all_goals assumption)
end
