module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.HermitianCurvature.BigCellVanishingOfCommute
public import Formalism.HermitianCurvature.CompositeFormulaLevelZero
public import Formalism.HermitianCurvature.StatementNF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.Bundle004
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

section

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have heI : ∀ (a : Fin r) (h : (a : ℕ) + 1 < r), eI k r a ≠ eI k r ⟨a + 1, h⟩ := by
    intro a h he
    have := congrArg Fin.val he
    simp [eI] at this
  have hz' : ∀ a : Fin r, z (eI k r a) = 0 := fun a => hz _ (Or.inl (by simp [eI]))
  simp [psi, ell, Matrix.one_apply_ne, heI, hz']

end Formalism.FourierDecayAlt.P.BesselCapelliCommutation

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {N : ℕ}

theorem pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩

theorem pd_const (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp

theorem pd_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => g i j) := by
  refine ⟨MvPolynomial.X (Sum.inl (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_star_entry (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

theorem pd_add {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g + Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p + q, (MvPolynomial.totalDegree_add p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_add]

theorem pd_mul {a b : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg b Q) :
    U.IsPolyDeg (a + b) (fun g => P g * Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p * q, (MvPolynomial.totalDegree_mul p q).trans (Nat.add_le_add hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_mul]

theorem pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by
  obtain ⟨p, hp, hpP⟩ := hP
  obtain ⟨q, hq, hqQ⟩ := hQ
  refine ⟨p - q, (MvPolynomial.totalDegree_sub p q).trans (max_le hp hq), fun g => ?_⟩
  dsimp only
  rw [hpP g, hqQ g, MvPolynomial.eval_sub]

theorem pd_sum {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg a (fun g => ∑ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 0 a
  | insert x s hx ih =>
    have h1 := pd_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert hx] using h1

theorem pd_prod {ι : Type*} (s : Finset ι) {a : ℕ} {P : ι → Matrix (Fin N) (Fin N) ℂ → ℂ}
    (h : ∀ i ∈ s, U.IsPolyDeg a (P i)) : U.IsPolyDeg (s.card * a) (fun g => ∏ i ∈ s, P i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pd_const (N := N) 1 0
  | insert x s hx ih =>
    have h1 := pd_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hc : (insert x s).card * a = a + s.card * a := by
      rw [Finset.card_insert_of_notMem hx]; ring
    rw [hc]
    simpa [Finset.prod_insert hx] using h1

theorem pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by
  have key : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin l))),
      U.IsPolyDeg l (fun g => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M g (σ i) i) := by
    intro σ _
    have h1 := pd_mul (pd_const (N := N) ((Equiv.Perm.sign σ : ℤ) : ℂ) 0)
      (pd_prod (Finset.univ : Finset (Fin l)) (fun i _ => h (σ i) i))
    refine pd_mono ?_ h1
    simp
  have h2 := pd_sum _ key
  simpa [Matrix.det_apply'] using h2

end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

namespace Formalism.FourierDecayAlt.P

open PartialDerivativeAlgebra

theorem gram_function_last_minor : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith

private theorem isPolyDeg_one_mulVec_apply {M : ℕ} (v : Fin M → ℂ) (j : Fin M) :
    U.IsPolyDeg 1 (fun g : Matrix (Fin M) (Fin M) ℂ => Matrix.mulVec g v j) := by
  have h := pd_sum (N := M) (Finset.univ : Finset (Fin M))
    (P := fun m g => g j m * v m) (a := 1 + 0)
    (fun m _ => pd_mul (pd_entry j m) (pd_const (v m) 0))
  simpa [Matrix.mulVec, dotProduct] using h

theorem zhat_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => Zhat k r z z' g a b) := by
  have hH : ∀ i, U.IsPolyDeg 1
      (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) := by
    intro i
    have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
      (P := fun j g => Hpk k r i j * Matrix.mulVec g (fvec k r z' b) j) (a := 0 + 1)
      (fun j _ => pd_mul (pd_const (Hpk k r i j) 0) (isPolyDeg_one_mulVec_apply _ j))
    simpa [Matrix.mulVec, dotProduct] using h
  have h := pd_sum (Finset.univ : Finset (Fin (2 * r + k + 1)))
    (P := fun i g => star (fvec k r z a i) * Matrix.mulVec (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) i) (a := 0 + 1)
    (fun i _ => pd_mul (pd_const _ 0) (hH i))
  simpa [Zhat, herm, dotProduct] using h

private theorem isPolyDeg_star' {M a : ℕ} {P : Matrix (Fin M) (Fin M) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) q), ?_, fun g => ?_⟩
  · have hm : (map (starRingEnd ℂ) q).totalDegree ≤ q.totalDegree := by
      unfold totalDegree; exact Finset.sup_mono (support_map_subset _ _)
    exact (totalDegree_rename_le _ _).trans (hm.trans hq)
  · dsimp only
    rw [hP g, eval_rename, eval_map]
    change starRingEnd ℂ (eval₂ (RingHom.id ℂ) _ q) = _
    rw [eval₂_comp_left, RingHom.comp_id]
    congr 1
    funext x
    rcases x with x | x <;> simp

theorem zhat_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (a b : Fin (r + 1)) :
    U.IsPolyDeg 1 (fun g => star (Zhat k r z z' g a b)) := by
  exact isPolyDeg_star' (zhat_pd k r z z' a b)

theorem minor_polynomial_property : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)

theorem dmin_star_pd (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    U.IsPolyDeg l.val (fun g => star (Dmin k r z z' g l)) := by
  exact isPolyDeg_star' (minor_polynomial_property k r z z' l)

theorem gram_function_polynomial : C6.GfPoly := by
  intro k r z z'
  have hL := pd_mul (minor_polynomial_property k r z z' (Fin.last (r + 1)))
    (dmin_star_pd k r z z' (Fin.last (r + 1)))
  have hR0 := pd_mul (minor_polynomial_property k r z z' ⟨r, by omega⟩)
    (dmin_star_pd k r z z' ⟨r, by omega⟩)
  have hR := pd_mul (pd_const (((Tz k r z * Tz k r z' : ℝ)) : ℂ) 0) hR0
  have hL' : U.IsPolyDeg (2 * r + 2) (fun g => Dmin k r z z' g (Fin.last (r + 1)) *
      star (Dmin k r z z' g (Fin.last (r + 1)))) :=
    pd_mono (by simp; omega) hL
  have hR' : U.IsPolyDeg (2 * r + 2) (fun g => ((Tz k r z * Tz k r z' : ℝ) : ℂ) *
      (Dmin k r z z' g ⟨r, by omega⟩ * star (Dmin k r z z' g ⟨r, by omega⟩))) :=
    pd_mono (by simp; omega) hR
  have h := pd_sub hL' hR'
  convert h using 2 with g
  simp only [Gf, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def, Complex.mul_conj]

end Formalism.FourierDecayAlt.P
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T

theorem isClosed_nonneg_complex : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)

theorem integral_nonneg_complex {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℂ)
    (h : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂ν := by
  have hre : ∀ a, f a = ((f a).re : ℂ) := fun a => by
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      exact ((Complex.le_def.mp (h a)).2).symm
  have hf : (fun a => f a) = fun a => ((f a).re : ℂ) := funext hre
  rw [hf]
  first
  | rw [integral_complex_ofReal]
  | rw [integral_ofReal]
  | rw [← RCLike.ofReal_eq_complex_ofReal, integral_ofReal]
  exact Complex.zero_le_real.mpr (integral_nonneg fun a => (Complex.le_def.mp (h a)).1)

theorem continuous_fsv (s : ℂ) : Continuous (fsv s) := by
  unfold fsv
  exact ((continuous_const.mul continuous_id).sub
    (continuous_const.mul Complex.continuous_conj)).cexp

theorem nonneg_of_continuous {φ : ℂ → ℂ} (hc : Continuous φ) (h : ∀ t, t ≠ 0 → 0 ≤ φ t) :
    ∀ t, 0 ≤ φ t := by
  have hcl : IsClosed {t | 0 ≤ φ t} := isClosed_nonneg_complex.preimage hc
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {t | 0 ≤ φ t} := fun t ht => h t ht
  have hcl2 := hcl.closure_subset_iff.mpr hsub
  rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at hcl2
  intro t
  exact hcl2 (Set.mem_univ t)

theorem eq_of_continuous_off_zero {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ t, t ≠ 0 → f t = g t) : f = g := hf.ext_on (dense_compl_singleton (0 : ℂ)) hg (fun t ht => h t ht)

theorem update_mem_OmX {m : ℕ} {c : Fin m → ℂ} (hc : c ∈ OmX m) (l : Fin m) {t : ℂ} (ht : t ≠ 0) :
    Function.update c l t ∈ OmX m := by
  intro j
  rcases eq_or_ne j l with rfl | hj
  · simpa using ht
  · rw [Function.update_of_ne hj]
    exact hc j

theorem nonneg_all_levels {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S]
    [DecidableEq S] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hTI : TopIdent (S := S) P z z' π π' μ L st K l0) (hTN : TopDensNonneg (S := S) P z z' π π' L st K l0)
    (hSI : SliceIn (S := S) P z z' π π' L st K l0) (hSD : StepDens (S := S) P z z' π π' μ L st K l0)
    (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w) :
    ∀ (n : ℕ) (i : Fin (P.r + 1)), i.val + n = P.r → ∀ c ∈ OmX P.r,
      ∀ x : Ix S → RadSp P.k P.r z z' π π', InK (K i) x → 0 ≤ RRform L st μ i w x x c := by
  intro n
  induction n with
  | zero =>
    intro i hi c hc x hx
    have hi' : i = Fin.last P.r := Fin.ext (by simpa using hi)
    subst hi'
    rw [(hTI w hw x x hx hx c hc).2]
    exact integral_nonneg_complex μ _ (fun g => hTN w hw x hx c hc (Matrix.of g))
  | succ n ih =>
    intro i hi c hc x hx
    have hlt : i.val < P.r := by omega
    obtain ⟨l, rfl⟩ : ∃ l : Fin P.r, l.castSucc = i := ⟨⟨i.val, hlt⟩, Fin.ext rfl⟩
    obtain ⟨φ, hφc, hφ, -, hint⟩ := hSD w hw l x x hx hx c hc
    rw [← hint]
    apply integral_nonneg_complex
    apply nonneg_of_continuous hφc
    intro t ht
    rw [hφ t ht]
    unfold ph
    apply mul_nonneg
    · exact Complex.zero_le_real.mpr (by positivity)
    · have hn : (l.succ).val + n = P.r := by
        simp only [Fin.coe_castSucc] at hi
        simp only [Fin.val_succ]
        omega
      exact ih l.succ hn _ (update_mem_OmX hc l ht) _ (hSI w hw l x hx)

theorem thmPFromStepsAll : ThmPFromStepsAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' μ L st K l0
  intro hTI hTN hTT hSI hSD hST hFS w hw
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy c hc
    refine ⟨(hTI w hw x y hx hy c hc).1, ?_, ?_⟩
    · intro s Wv Wv' h1 h2
      obtain ⟨hK, hD⟩ := hTT w hw s Wv Wv' h1 h2 x y hx hy c hc
      rw [(hTI w hw _ y hK hy c hc).2]
      congr 1
      funext g
      rw [hD]
    · exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw 0
        (Fin.last P.r) (by simp) c hc x hx
  · intro l x y hx hy c hc
    obtain ⟨φ, hφc, hφ, hC, -⟩ := hSD w hw l x y hx hy c hc
    refine ⟨φ, hφc, hφ, hC, ?_⟩
    intro s Wv Wv' h1 h2
    obtain ⟨hK, hT⟩ := hST w hw l s Wv Wv' h1 h2 x y hx hy c hc
    obtain ⟨ψ, hψc, hψ, -, hψint⟩ := hSD w hw l _ y hK hy c hc
    rw [← hψint]
    congr 1
    apply eq_of_continuous_off_zero ((continuous_fsv s).mul hφc) hψc
    intro t ht
    show fsv s t * φ t = ψ t
    rw [hψ t ht, hT t ht, hφ t ht]
  · intro i c hc
    refine ⟨hFS w hw i c hc, ?_⟩
    intro x hx
    have hxK : InK (K i) x := fun a => (Submodule.mem_pi.mp hx) a (Set.mem_univ a)
    exact nonneg_all_levels (S := S) P z z' π π' μ L st K l0 hTI hTN hSI hSD w hw (P.r - i.val) i
      (by omega) c hc x hxK

end Formalism.FourierDecayAlt.P5
end
end

section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem cf_last_isEmpty (r : ℕ) : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩

theorem integrable_cf_last {r : ℕ} (f : Cf r (Fin.last r) → ℂ) : Integrable f := by
  haveI := cf_last_isEmpty r
  have hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l) := by
    rw [volume_pi, Measure.pi_of_empty]
  haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance
  have hf : f = fun _ => f (fun l => isEmptyElim l) := by
    funext c'
    congr 1
    funext l
    exact isEmptyElim l
  rw [hf]
  exact integrable_const _

end Formalism.FourierDecayAlt.P5.HerC
end
end

section

open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_neg_fst (a : Pr V) : (-a).1 = -a.1 := rfl
theorem pr_neg_snd (a : Pr V) : (-a).2.unop = -a.2.unop := rfl

end PairNeg

end Formalism.FourierDecayAlt.P5
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

section Wirt

theorem dZ_eq (f : ℂ → ℂ) (c : ℂ) : NF.dZ f c = (1 / 2 : ℂ) * (fderiv ℝ f c 1 - Complex.I * fderiv ℝ f c Complex.I) := rfl

theorem dZ_conj {φ : ℂ → ℂ} {c : ℂ} (h : DifferentiableAt ℝ φ c) :
    NF.dZ (fun w => conj (φ w)) c = conj (NF.dZb φ c) := by
  have hd : HasFDerivAt (fun w => conj (φ w)) ((Complex.conjCLE.toContinuousLinearMap).comp (fderiv ℝ φ c)) c :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp c h.hasFDerivAt
  unfold NF.dZ NF.dZb
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    map_add, map_sub, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

end Wirt

section IBP

end IBP

section Cpt

end Cpt

end Formalism.FourierDecayAlt.P5.HerB
end
end
