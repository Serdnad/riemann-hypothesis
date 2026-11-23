module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle660
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle651
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle589
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle636
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

private theorem map_smul_ringHom' {n : Type} {α β : Type} [CommRing α] [CommRing β] (F : α →+* β) (c : α)
    (M : Matrix n n α) : (c • M).map F = F c • M.map F :=
  Matrix.map_smul' F c M (map_mul F)

private theorem smul_cancel' {n : Type} {D : Type} [CommRing D] {c : D} (hc : c ∈ nonZeroDivisors D)
    {M M' : Matrix n n D} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 this

private theorem alg' {n : Type} [Fintype n] [DecidableEq n] {D : Type} [CommRing D] (Φ : D →+* D)
    (L pf pg fE gE : D) (a N : ℕ) (xf xg Af Ag ε Fm : Matrix n n D)
    (h1f : (L * pf ^ N) • (xf * Af) = fE ^ (a + 2 * N) • (Fm * xf.map Φ))
    (h1g : (L * pg ^ N) • (xg * Ag) = gE ^ (a + 2 * N) • (Fm * xg.map Φ))
    (hR : gE ^ N • (xf * ε) = fE ^ N • xg) (hpf : Φ fE = pf) (hpg : Φ gE = pg) :
    (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ))) =
      (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
  have hΦR : pg ^ N • (xf.map Φ * ε.map Φ) = pf ^ N • xg.map Φ := by
    have := congrArg (fun M => M.map Φ) hR
    simpa only [map_smul_ringHom', Matrix.map_mul, map_pow, hpf, hpg] using this
  calc (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ)))
      = (pg ^ N * gE ^ (a + 2 * N)) • (((L * pf ^ N) • (xf * Af)) * ε.map Φ) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (pg ^ N * gE ^ (a + 2 * N)) • ((fE ^ (a + 2 * N) • (Fm * xf.map Φ)) * ε.map Φ) := by rw [h1f]
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pg ^ N • (xf.map Φ * ε.map Φ))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pf ^ N • xg.map Φ)) := by rw [hΦR]
    _ = (fE ^ (a + 2 * N) * pf ^ N) • (gE ^ (a + 2 * N) • (Fm * xg.map Φ)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + 2 * N) * pf ^ N) • ((L * pg ^ N) • (xg * Ag)) := by rw [h1g]
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((fE ^ N • xg) * Ag) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((gE ^ N • (xf * ε)) * Ag) := by rw [hR]
    _ = (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring

theorem rel_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  intro l _ K bk d ρ τ s ht hτ B f₀ hE f g ε hR Φ hΦ

  have hρpos : 0 < bk.ρ₀ := by
    unfold BK.ρ₀; exact NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hρle : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      (by have : (0 : ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
          linarith)

  have hnS : ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
    rw [frobS_X]
    refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l hρpos).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρle) (Fact.out : l.Prime).ne_zero
  have hΦS := isDiscMap_map (frobS l bk.a) hnS

  have key : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      (((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) ^ s.N) •
        (ht.bas.map Fh * (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) =
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) * (ht.bas.map Fh).map Φ)) := by
    intro h Fh hFh
    have hφ : ∀ x, BK.hf h (frobS l bk.a x) = B.D.φ (BK.hf h x) := fun x => h.f_φ x
    have c1 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Φ.comp Fh) :=
      ⟨fun x => by simp [hFh.ext, hΦ.ext], fun x => (hΦ.norm_le _).trans (hFh.norm_le _)⟩
    have c2 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Fh.comp (Disc.map (frobS l bk.a) hnS)) :=
      ⟨fun x => by simp [hFh.ext, hΦS.ext, hφ], fun x => (hFh.norm_le _).trans (hΦS.norm_le _)⟩
    have hc : Φ.comp Fh = Fh.comp (Disc.map (frobS l bk.a) hnS) := c1.unique c2
    have hP := congrArg (fun M => M.map Fh) (GlobalTheory.T.latticeBasis_frobenius_equation_disc l K bk d ρ τ s ht hτ _ hΦS)
    simp only [map_smul_ringHom', Matrix.map_mul, Matrix.map_map, map_mul, map_pow, map_natCast] at hP
    have eA : (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) = ht.A.map (Fh ∘ toDisc l (X : bk.S) bk.ρ₀) := by
      ext i j; exact (hFh.ext _).symm
    have eF : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) =
        s.F.map (Fh ∘ (toDisc l (X : bk.S) bk.ρ₀).comp C) := by
      ext i j; exact (hFh.ext _).symm
    have eB : (ht.bas.map Fh).map Φ = ht.bas.map (Fh ∘ Disc.map (frobS l bk.a) hnS) := by
      ext i j; exact RingHom.congr_fun hc _
    have e1 : toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) = Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) :=
      ((hFh.ext _).trans (congrArg _ (hφ _))).symm
    have e2 : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = Fh (toDisc l (X : bk.S) bk.ρ₀ bk.E) := (hFh.ext _).symm
    simp only [eA, eF, eB, e1, e2]
    exact hP

  have hn := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀
  have hFf := isDiscMap_map (BK.hf f) (hn f).1
  have hFg := isDiscMap_map (BK.hf g) (hn g).1
  have h1f := key f _ hFf
  have h1g := key g _ hFg
  have hFm : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf g).comp C)) = s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf f).comp C)) := by
    congr 1; funext w; simp [GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt l K bk B f g w]
  simp only [hFm] at h1g

  have hreg : ∀ h : Hom bk.prism B, toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    intro h
    obtain ⟨v, hv⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ h).2.1
    have e : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) * toDisc l (BK.hf f₀ X) bk.ρ₀ (v : B.A) :=
      (congrArg _ hv).symm.trans (map_mul _ _ _)
    exact (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) e).mpr
      (Submonoid.mul_mem _ hE ((v.isUnit.map (toDisc l (BK.hf f₀ X) bk.ρ₀)).mem_nonZeroDivisors))
  have hunit : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      IsUnit (toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E))) := by
    intro h Fh hFh
    have := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map Fh
    have e : Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) :=
      (hFh.ext _).trans (congrArg _ (h.f_φ _))
    exact (congrArg IsUnit e).mp this
  have hpf : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) := hΦ.ext _
  have hpg : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) := hΦ.ext _
  have hAlg := alg' Φ _ _ _ _ _ _ _ _ _ _ _ _ _ h1f h1g (hR _ _ hFf hFg) hpf hpg
  have hc : ((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) ^ s.N *
      toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) ^ s.N * toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ s.N) ∈ nonZeroDivisors _ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) (pow_mem (hreg g) _)
    · exact ((isUnit_l_disc l (BK.hf f₀ X) bk.ρ₀).pow _).mem_nonZeroDivisors
    · exact ((hunit f _ hFf).pow _).mem_nonZeroDivisors
    · exact ((hunit g _ hFg).pow _).mem_nonZeroDivisors
  have hM := smul_cancel' hc hAlg
  have hF0 : Disc.map (BK.hf f) (hn f).1 (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors _ :=
    (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) (hFf.ext bk.E)).mpr (hreg f)
  have := GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht _ _ hF0 _ _ hM
  exact this

end GlobalTheory.BSP.Height
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobValue

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem hf_comp {Q Q' : Obj l ↥(OL K)} (c : Hom Q Q') (g : Hom bk.prism Q) :
    BK.hf (c.comp g) = c.f.comp (BK.hf g) := rfl

theorem frob_change (S : Strat bk d) {Q : Obj l ↥(OL K)} (g g' : Hom bk.prism Q) (y y' : Fin d → Q.A)
    (hy : y = (S.ε g g').mulVec y') :
    BK.hf g' bk.E ^ S.a • (S.A.map (BK.hf g)).mulVec (fun i => Q.D.φ (y i)) =
      BK.hf g bk.E ^ S.a • (S.ε g g').mulVec ((S.A.map (BK.hf g')).mulVec (fun i => Q.D.φ (y' i))) := by
  have e : (fun i => Q.D.φ (y i)) = ((S.ε g g').map Q.D.φ).mulVec (fun i => Q.D.φ (y' i)) := by
    funext i; rw [hy, RingHom.map_mulVec]; rfl
  rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec,
    S.ε_φ]

theorem push (S : Strat bk d) {C Q : Obj l ↥(OL K)} (p : Hom C Q) (f : Hom bk.prism C) (c : C.A)
    (y : Fin d → C.A) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i)) =
      p.f c ^ S.a • (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) := by
  funext i
  have h1 : p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j))) i) =
      p.f c ^ S.a * p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) := by
    rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  have h2 : p.f ((S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (y j)) i) =
      (S.A.map (BK.hf (p.comp f))).mulVec (fun j => Q.D.φ (p.f (y j))) i := by
    rw [RingHom.map_mulVec, Matrix.map_map, hf_comp]
    congr 1
    funext j
    exact p.f_φ (y j)
  refine h1.trans ?_
  simp only [h2, Pi.smul_apply, smul_eq_mul]

theorem vec_cancel {A : Type} [CommRing A] {r : A} (hr : r ∈ nonZeroDivisors A) {u w : Fin d → A}
    (e : r • u = r • w) : u = w :=
  funext fun i => (mul_cancel_left_mem_nonZeroDivisors hr).1 (congrFun e i)

theorem pow_smul_transfer_of_regular {A : Type} [CommRing A] {a : ℕ} {e e' u u' : A} {L R : Fin d → A}
    (hr : e ^ a * e' ^ a ∈ nonZeroDivisors A) (hF : e' ^ a • L = e ^ a • R) (hT : u * e = u' * e') :
    u ^ a • L = u' ^ a • R := by
  refine vec_cancel hr ?_
  calc (e ^ a * e' ^ a) • (u ^ a • L) = (u * e) ^ a • (e' ^ a • L) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring
    _ = (u' * e') ^ a • (e ^ a • R) := by rw [hF, hT]
    _ = (e ^ a * e' ^ a) • (u' ^ a • R) := by
        rw [smul_smul, smul_smul, mul_pow]; congr 1; ring

theorem compat (S : Strat bk d) {B C Q : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (hn : ∀ g : Hom bk.prism Q, BK.hf g bk.E ∈ nonZeroDivisors Q.A)
    (x : N) (p q : Hom C Q) (hpq : p.comp h = q.comp h) :
    (fun i => p.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) =
      (S.ε (p.comp f) (q.comp f)).mulVec
        (fun i => q.f ((c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun j => C.D.φ (V.v h f x j))) i)) := by
  have hY : ∀ j, p.f (V.v h f x j) = V.v (p.comp h) (p.comp f) x j :=
    fun j => (V.v_nat p h f x j).symm
  have hY' : ∀ j, q.f (V.v h f x j) = V.v (p.comp h) (q.comp f) x j := by
    rw [hpq]; exact fun j => (V.v_nat q h f x j).symm
  have hF := frob_change S (p.comp f) (q.comp f) _ _ (V.v_ε (p.comp h) (p.comp f) (q.comp f) x)
  have hT : p.f c * BK.hf (p.comp f) bk.E = q.f c * BK.hf (q.comp f) bk.E := by
    have e1 : p.f (c * BK.hf f bk.E) = q.f (c * BK.hf f bk.E) := by
      rw [hc]; exact congrArg (fun k : Hom B Q => k.f t) hpq
    simpa only [map_mul, hf_comp, RingHom.comp_apply] using e1
  rw [push S p f c, push S q f c, Matrix.mulVec_smul]
  simp only [hY, hY']
  exact pow_smul_transfer_of_regular (mul_mem (pow_mem (hn (p.comp f)) S.a) (pow_mem (hn (q.comp f)) S.a)) hF hT

theorem pow_smul_matrix_swap_of_relation {A : Type} [CommRing A] {a : ℕ} {e e' u : A} {L M : Fin d → A} {P : Matrix (Fin d) (Fin d) A}
    (hF : e' ^ a • L = e ^ a • P.mulVec M) : e ^ a • P.mulVec (u ^ a • M) = (u * e') ^ a • L := by
  rw [Matrix.mulVec_smul, mul_pow, mul_smul, hF, smul_comm]

theorem coord (S : Strat bk d) {B C Q Q' : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C) (c : C.A) (t : B.A) (hc : c * BK.hf f bk.E = h.f t)
    (a : Hom B Q) (g : Hom bk.prism Q) (h' : Hom Q Q') (a' : Hom C Q') (hcomm : a'.comp h = h'.comp a)
    (hinj' : Function.Injective h'.f) (x w : N)
    (hw : V.v h f w = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i))) :
    BK.hf g bk.E ^ S.a • V.v a g w = a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i) := by
  have nat' : ∀ (y : N) j, h'.f (V.v a g y j) = V.v (a'.comp h) (h'.comp g) y j := by
    intro y j; rw [hcomm]; exact (V.v_nat h' a g y j).symm
  have natC : ∀ (y : N) j, a'.f (V.v h f y j) = V.v (a'.comp h) (a'.comp f) y j :=
    fun y j => (V.v_nat a' h f y j).symm
  have ht : h'.f (a.f t) = a'.f c * BK.hf (a'.comp f) bk.E := by
    have e : h'.f (a.f t) = a'.f (h.f t) := congrArg (fun k : Hom B Q' => k.f t) hcomm.symm
    rw [e, ← hc, map_mul]; rfl
  have e1 : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      BK.hf (h'.comp g) bk.E ^ S.a • V.v (a'.comp h) (h'.comp g) w := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, nat']
    rfl
  have e2 : V.v (a'.comp h) (a'.comp f) w =
      a'.f c ^ S.a • (S.A.map (BK.hf (a'.comp f))).mulVec fun j => Q'.D.φ (V.v (a'.comp h) (a'.comp f) x j) := by
    have e := push S a' f c (V.v h f x)
    rw [← hw] at e
    simp only [natC] at e
    exact e
  have e3 := push S h' g (a.f t) (V.v a g x)
  simp only [nat', ht] at e3
  have hF := frob_change S (h'.comp g) (a'.comp f) _ _ (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) x)
  have key : (fun i => h'.f ((BK.hf g bk.E ^ S.a • V.v a g w) i)) =
      fun i => h'.f ((a.f t ^ S.a • (S.A.map (BK.hf g)).mulVec fun j => Q.D.φ (V.v a g x j)) i) := by
    have v1 := (V.v_ε (a'.comp h) (h'.comp g) (a'.comp f) w).trans (congrArg _ e2)
    exact e1.trans ((congrArg (fun v => BK.hf (h'.comp g) bk.E ^ S.a • v) v1).trans ((pow_smul_matrix_swap_of_relation hF).trans e3.symm))
  funext i
  exact hinj' (congrFun key i)

theorem psi_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (t : B.A), t ∈ B.I →
    ∃ Ψ : N →ₛₗ[B.D.φ] N, IsPsi V t Ψ := by
  intro l _ K bk d S B N _ _ V t ht
  obtain ⟨C, h, ⟨f⟩, hC⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  have hIC := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C f).1
  have htC : h.f t ∈ Ideal.span {BK.hf f bk.E} := hIC ▸ h.f_I t ht
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 htC
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B C N V h f hC
  have hzc : ∀ x : N, ∃ y, V.v h f y = c ^ S.a • (S.A.map (BK.hf f)).mulVec (fun i => C.D.φ (V.v h f x i)) :=
    fun x => hsurj _ fun Q p q hpq =>
      compat S V h f c t hc (fun g => (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk Q g).2) x p q hpq
  choose Ψf hΨf using hzc
  have zadd : ∀ x y : N, Ψf (x + y) = Ψf x + Ψf y := by
    intro x y
    apply hinj
    have e1 : V.v h f (x + y) = V.v h f x + V.v h f y := map_add (V.v h f) x y
    have e2 : V.v h f (Ψf x + Ψf y) = V.v h f (Ψf x) + V.v h f (Ψf y) := map_add (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (x + y) i)) =
        (fun i => C.D.φ (V.v h f x i)) + (fun i => C.D.φ (V.v h f y i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans (C.D.φ.map_add _ _)
    refine (hΨf (x + y)).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (hΨf x) (hΨf y)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_add _ _ _)).trans (smul_add _ _ _)
  have zsmul : ∀ (b : B.A) (x : N), Ψf (b • x) = B.D.φ b • Ψf x := by
    intro b x
    apply hinj
    have e1 : V.v h f (b • x) = h.f b • V.v h f x := LinearMap.map_smulₛₗ (V.v h f) b x
    have e2 : V.v h f (B.D.φ b • Ψf x) = h.f (B.D.φ b) • V.v h f (Ψf x) := LinearMap.map_smulₛₗ (V.v h f) _ _
    have hφ : (fun i => C.D.φ (V.v h f (b • x) i)) = h.f (B.D.φ b) • (fun i => C.D.φ (V.v h f x i)) :=
      funext fun i => (congrArg (fun v : Fin d → C.A => C.D.φ (v i)) e1).trans
        ((C.D.φ.map_mul _ _).trans (congrArg (· * C.D.φ (V.v h f x i)) (h.f_φ b).symm))
    refine (hΨf (b • x)).trans (Eq.trans ?_ ((congrArg (h.f (B.D.φ b) • ·) (hΨf x)).symm.trans e2.symm))
    refine (congrArg (fun v => c ^ S.a • (S.A.map (BK.hf f)).mulVec v) hφ).trans ?_
    exact (congrArg (c ^ S.a • ·) (Matrix.mulVec_smul _ _ _)).trans (smul_comm _ _ _)
  refine ⟨{ toFun := Ψf, map_add' := zadd, map_smul' := zsmul }, ?_⟩
  intro Q a g x
  obtain ⟨Q', h', a', hcomm, hinj'⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hC Q a
  exact coord S V h f c t hc a g h' a' hcomm hinj' x (Ψf x) (hΨf x)

end GlobalTheory.BSP.FrobValue
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem stratHom_map_mulVec {m n : Type} [Fintype n] {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : Matrix m n A) (v : n → A) : (fun i => φ ((M.mulVec v) i)) = (M.map φ).mulVec (fun i => φ (v i)) := by
  funext i
  exact RingHom.map_mulVec φ M v i

theorem stratHom_coord_nat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    (Y : Matrix (Fin d') (Fin d) bk.S) {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) {Q Q' : Obj l ↥(OL K)} (r : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) :
    (fun i => r.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) i)) =
      (Y.map (BK.hf (r.comp g))).mulVec (V.v (r.comp a) (r.comp g) x) := by
  rw [stratHom_map_mulVec]
  have e1 : (Y.map (BK.hf g)).map r.f = Y.map (BK.hf (r.comp g)) := by
    rw [Matrix.map_map]; rfl
  have e2 : (fun i => r.f (V.v a g x i)) = V.v (r.comp a) (r.comp g) x := by
    funext i; exact (V.v_nat r a g x i).symm
  rw [e1, e2]

theorem stratHom_coord_ε {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    {S' : Strat bk d'} {Y : Matrix (Fin d') (Fin d) bk.S} (hY : IsStratHom S S' Y) {B : Obj l ↥(OL K)} {N : Type}
    [AddCommGroup N] [Module B.A N] (V : Eval S B N) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g g' : Hom bk.prism Q)
    (x : N) :
    (Y.map (BK.hf g)).mulVec (V.v a g x) = (S'.ε g g').mulVec ((Y.map (BK.hf g')).mulVec (V.v a g' x)) := by
  rw [V.v_ε a g g' x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY.ε]

theorem evalHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N]
    [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'),
    ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  intro l _ K bk d d' S S' Y hY B N _ _ N' _ _ V V'
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨inj, ev⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C N' V' h f hc
  have hz : ∀ x, ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h →
      (fun i => p.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i)) = (S'.ε (p.comp f) (q.comp f)).mulVec
        fun i => q.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i) := by
    intro x Q p q hpq
    have e : V.v (p.comp h) (p.comp f) x = V.v (q.comp h) (p.comp f) x := by rw [hpq]
    refine (stratHom_coord_nat Y V p h f x).trans ?_
    refine Eq.trans ?_ (congrArg (S'.ε (p.comp f) (q.comp f)).mulVec (stratHom_coord_nat Y V q h f x)).symm
    rw [e]
    exact stratHom_coord_ε hY V (q.comp h) (p.comp f) (q.comp f) x
  choose w0 hw0 using fun x => ev _ (hz x)
  let w : N →ₗ[B.A] N' :=
    { toFun := w0
      map_add' := fun x y => by
        apply inj
        show V'.v h f (w0 (x + y)) = V'.v h f (w0 x + w0 y)
        refine (hw0 (x + y)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_add (w0 x) (w0 y)).symm
        refine Eq.trans ?_ (congrArg₂ (· + ·) (hw0 x) (hw0 y)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_add x y)).trans (Matrix.mulVec_add _ _ _)
      map_smul' := fun c x => by
        apply inj
        show V'.v h f (w0 (c • x)) = V'.v h f (c • w0 x)
        refine (hw0 (c • x)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_smulₛₗ c (w0 x)).symm
        refine Eq.trans ?_ (congrArg (h.f c • ·) (hw0 x)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_smulₛₗ c x)).trans (Matrix.mulVec_smul _ _ _) }
  refine ⟨w, fun Q a g x => ?_⟩
  obtain ⟨Q', h', a', hcomm, hinj⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hc Q a
  have hw : w x = w0 x := rfl
  funext i
  apply hinj
  have lhs : (fun j => h'.f (V'.v a g (w0 x) j)) = V'.v (a'.comp h) (h'.comp g) (w0 x) := by
    exact (funext fun j => (V'.v_nat h' a g (w0 x) j).symm).trans
      (congrArg (fun t => V'.v t (h'.comp g) (w0 x)) hcomm.symm)
  have rhs : (fun j => h'.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) j)) =
      (Y.map (BK.hf (h'.comp g))).mulVec (V.v (a'.comp h) (h'.comp g) x) := by
    exact (stratHom_coord_nat Y V h' a g x).trans
      (congrArg (fun t => (Y.map (BK.hf (h'.comp g))).mulVec (V.v t (h'.comp g) x)) hcomm.symm)
  have mid : V'.v (a'.comp h) (a'.comp f) (w0 x) = (Y.map (BK.hf (a'.comp f))).mulVec (V.v (a'.comp h) (a'.comp f) x) := by
    exact (funext fun j => V'.v_nat a' h f (w0 x) j).trans
      ((congrArg (fun v : Fin d' → C.A => fun j => a'.f (v j)) (hw0 x)).trans (stratHom_coord_nat Y V a' h f x))
  have := congrFun (lhs.trans ((V'.v_ε (a'.comp h) (h'.comp g) (a'.comp f) (w0 x)).trans
    ((congrArg (S'.ε (h'.comp g) (a'.comp f)).mulVec mid).trans
      ((stratHom_coord_ε hY V (a'.comp h) (h'.comp g) (a'.comp f) x).symm.trans rhs.symm)))) i
  rw [hw]
  exact this

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem eval_transition_comp_assoc {l : ℕ} {R : Type} [CommRing R] {P P' P'' P''' : Obj l R}
    (c : Hom P'' P''') (b : Hom P' P'') (a : Hom P P') : c.comp (b.comp a) = (c.comp b).comp a :=
  Hom.ext' rfl

theorem eval_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N']
    [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'),
    ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (t x) = V.v (a.comp k) g x := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k
  obtain ⟨C', h', ⟨f'⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C' N' V' h' f' hc
  have hz : ∀ x : N, ∃ y, V'.v h' f' y = V.v (h'.comp k) f' x := by
    intro x
    apply hsurj
    intro Q p q hpq
    have e : p.comp (h'.comp k) = q.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, hpq, ← eval_transition_comp_assoc]
    have hp : (fun i => p.f (V.v (h'.comp k) f' x i)) = V.v (p.comp (h'.comp k)) (p.comp f') x :=
      funext fun i => (V.v_nat p (h'.comp k) f' x i).symm
    have hq : (fun i => q.f (V.v (h'.comp k) f' x i)) = V.v (q.comp (h'.comp k)) (q.comp f') x :=
      funext fun i => (V.v_nat q (h'.comp k) f' x i).symm
    rw [hp, hq, V.v_ε (p.comp (h'.comp k)) (p.comp f') (q.comp f') x, e]
  choose t0 ht0 using hz
  let t : N →ₛₗ[k.f] N' :=
    { toFun := t0
      map_add' := fun x y => hinj <|
        (ht0 (x + y)).trans ((LinearMap.map_add (V.v (h'.comp k) f') x y).trans
          ((congrArg₂ (· + ·) (ht0 x) (ht0 y)).symm.trans (LinearMap.map_add (V'.v h' f') (t0 x) (t0 y)).symm))
      map_smul' := fun c x => hinj <|
        (ht0 (c • x)).trans ((LinearMap.map_smulₛₗ (V.v (h'.comp k) f') c x).trans
          ((congrArg (h'.f (k.f c) • ·) (ht0 x)).symm.trans (LinearMap.map_smulₛₗ (V'.v h' f') (k.f c) (t0 x)).symm)) }
  have hT : ∀ x, V'.v h' f' (t x) = V.v (h'.comp k) f' x := ht0
  refine ⟨t, ?_, ?_⟩
  · haveI := V.fin; haveI := V.proj; haveI := V'.fin; haveI := V'.proj
    exact GlobalTheory.T.semilinear_projective_module_compose l (↥(OL K)) B' C' h' hc B.A k.f N N' (Fin d → C'.A) t (V'.v h' f')
      (V.v (h'.comp k) f') (fun x => (hT x).symm) (V'.bc h' f') (V.bc (h'.comp k) f')
  · intro Q a g x
    obtain ⟨Q'', h'', a', hsq, hinj''⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B' C' h' hc Q a
    have e2 : h''.comp (a.comp k) = a'.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, ← hsq, ← eval_transition_comp_assoc]
    have key : V'.v (a'.comp h') (a'.comp f') (t x) = V.v (a'.comp (h'.comp k)) (a'.comp f') x :=
      funext fun j => (V'.v_nat a' h' f' (t x) j).trans ((congrArg a'.f (congrFun (hT x) j)).trans (V.v_nat a' (h'.comp k) f' x j).symm)
    funext i
    apply hinj''
    calc h''.f (V'.v a g (t x) i) = V'.v (h''.comp a) (h''.comp g) (t x) i := (V'.v_nat h'' a g (t x) i).symm
      _ = V'.v (a'.comp h') (h''.comp g) (t x) i := congrArg (fun c => V'.v c (h''.comp g) (t x) i) hsq.symm
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V'.v (a'.comp h') (a'.comp f') (t x)) i :=
          congrFun (V'.v_ε (a'.comp h') (h''.comp g) (a'.comp f') (t x)) i
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V.v (a'.comp (h'.comp k)) (a'.comp f') x) i :=
          congrArg (fun w => (S.ε (h''.comp g) (a'.comp f')).mulVec w i) key
      _ = V.v (a'.comp (h'.comp k)) (h''.comp g) x i :=
          (congrFun (V.v_ε (a'.comp (h'.comp k)) (h''.comp g) (a'.comp f') x) i).symm
      _ = V.v (h''.comp (a.comp k)) (h''.comp g) x i := congrArg (fun c => V.v c (h''.comp g) x i) e2.symm
      _ = h''.f (V.v (a.comp k) g x i) := V.v_nat h'' (a.comp k) g x i

end GlobalTheory.BSP
end
end
