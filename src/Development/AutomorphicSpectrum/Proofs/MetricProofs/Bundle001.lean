module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Complex.Schwarz
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.UnitQuotients

theorem consecutive_quotients_units :
    ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (N : ℕ) (G E : Fin N → Φ), (∀ i, E i ≠ 0) → (∀ i, (∏ k ∈ Finset.Iic i, G k) / E i ≠ 0 ∧ (∏ k ∈ Finset.Iic i, G k) / E i ∈ R ∧ ((∏ k ∈ Finset.Iic i, G k) / E i)⁻¹ ∈ R) → ∀ i : Fin N, G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ≠ 0 ∧ G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩) ∈ R ∧ (G i / (if h : (i : ℕ) = 0 then E i else E i / E ⟨(i : ℕ) - 1, by have := i.2; omega⟩))⁻¹ ∈ R := by
  intro Φ _ R N G E hE hU i
  by_cases h : (i : ℕ) = 0
  · have hI : Finset.Iic i = {i} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hk
        apply Fin.ext
        have : (k : ℕ) ≤ i := hk
        omega
      · rintro rfl
        exact le_rfl
    have hi := hU i
    rw [hI, Finset.prod_singleton] at hi
    simpa only [dif_pos h] using hi
  · simp only [dif_neg h]
    have hlt : (i : ℕ) - 1 < N := by have := i.2; omega
    generalize hj : (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = j
    have hjv : (j : ℕ) = (i : ℕ) - 1 := by rw [← hj]
    have hI : Finset.Iic i = insert i (Finset.Iic j) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hk
        have hk' : (k : ℕ) ≤ i := hk
        by_cases hki : k = i
        · exact Or.inl hki
        · right
          have : (k : ℕ) ≠ i := fun e => hki (Fin.ext e)
          show (k : ℕ) ≤ j
          omega
      · rintro (rfl | hk)
        · exact le_rfl
        · have hk' : (k : ℕ) ≤ j := hk
          show (k : ℕ) ≤ i
          omega
    have hnot : i ∉ Finset.Iic j := by
      simp only [Finset.mem_Iic]
      intro hij
      have : (i : ℕ) ≤ j := hij
      omega
    obtain ⟨a0, a1, a2⟩ := hU i
    obtain ⟨b0, b1, b2⟩ := hU j
    rw [hI, Finset.prod_insert hnot] at a0 a1 a2
    generalize (∏ k ∈ Finset.Iic j, G k) = D at a0 a1 a2 b0 b1 b2
    have hD : D ≠ 0 := fun e => b0 (by rw [e, zero_div])
    have hEi := hE i
    have hEj := hE j
    have key : G i / (E i / E j) = (G i * D / E i) * (D / E j)⁻¹ := by
      field_simp
    rw [key]
    refine ⟨mul_ne_zero a0 (inv_ne_zero b0), R.mul_mem a1 b2, ?_⟩
    rw [mul_inv, inv_inv]
    exact R.mul_mem a2 b1

end GlobalTheory.CompanionTheory.Metric.UnitQuotients
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.Telescope

theorem fin_iic_telescope : ∀ (N : ℕ) (M : Type) [AddCommGroup M] (f : Fin N → M) (i : Fin N),
    f i = -∑ k ∈ Finset.Iic i, (if h : (k : ℕ) = 0 then -f k else
      f ⟨(k : ℕ) - 1, by have := k.2; omega⟩ - f k) := by
  intro N M _ f i
  obtain ⟨n, hn⟩ := i
  induction n with
  | zero =>
    have hset : Finset.Iic (⟨0, hn⟩ : Fin N) = {⟨0, hn⟩} := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_singleton, dite_eq_left rfl, neg_neg]
  | succ n ih =>
    have hn' : n < N := by omega
    have hset : Finset.Iic (⟨n + 1, hn⟩ : Fin N) = insert ⟨n + 1, hn⟩ (Finset.Iic ⟨n, hn'⟩) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
      omega
    have hnot : (⟨n + 1, hn⟩ : Fin N) ∉ Finset.Iic ⟨n, hn'⟩ := by
      simp only [Finset.mem_Iic, Fin.le_iff_val_le_val, not_le]
      omega
    have hs := (neg_eq_iff_eq_neg.mpr (ih hn')).symm
    rw [hset, Finset.sum_insert hnot, dite_eq_right (by simp), hs]
    have e : ∀ p, f ⟨(⟨n + 1, hn⟩ : Fin N).val - 1, p⟩ = f ⟨n, hn'⟩ :=
      fun p => congrArg f (Fin.ext (by simp))
    rw [e]
    abel

end GlobalTheory.CompanionTheory.Metric.Telescope
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Metric.GradedLines

theorem prod_Iic_eq_prod_castLE {Φ : Type} [CommMonoid Φ] {N : ℕ} (G : Fin N → Φ)
    (i : Fin N) (n : ℕ) (hn : n ≤ N) (hin : n = (i : ℕ) + 1) :
    ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin n, G (Fin.castLE hn l) := by
  symm
  refine Finset.prod_bij (fun l _ => Fin.castLE hn l) ?_ ?_ ?_ ?_
  · intro l _
    have := l.2
    simp only [Finset.mem_Iic, Fin.le_def, Fin.val_castLE]
    omega
  · intro a _ b _ hab
    exact Fin.castLE_injective hn hab
  · intro b hb
    have hb' : (b : ℕ) ≤ (i : ℕ) := Fin.le_def.mp (Finset.mem_Iic.mp hb)
    refine ⟨⟨(b : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    ext
    simp
  · intro _ _
    rfl

theorem prod_first_graded_lines :
    ∀ (Φ : Type) [CommMonoid Φ] (p q : ℕ) (tW : Fin p → Φ) (tO : Fin q → Φ) (G : Fin (p + q) → Φ), (∀ (i : Fin (p + q)) (h : (i : ℕ) < p), G i = tW ⟨i, h⟩) → (∀ (i : Fin (p + q)) (h : p ≤ (i : ℕ)), G i = tO ⟨(i : ℕ) - p, by have := i.2; omega⟩) → ∀ i : Fin (p + q), (∀ h : (i : ℕ) < p, ∏ k ∈ Finset.Iic i, G k = ∏ l : Fin ((i : ℕ) + 1), tW (Fin.castLE h l)) ∧ (∀ h : p ≤ (i : ℕ), ∏ k ∈ Finset.Iic i, G k = (∏ l, tW l) * ∏ l : Fin ((i : ℕ) - p + 1), tO (Fin.castLE (by have := i.2; omega) l)) := by
  intro Φ _ p q tW tO G h1 h2 i
  constructor
  · intro h
    rw [prod_Iic_eq_prod_castLE G i ((i : ℕ) + 1) (by have := i.2; omega) rfl]
    refine Finset.prod_congr rfl fun l _ => ?_
    have hl : ((Fin.castLE (by have := i.2; omega) l : Fin (p + q)) : ℕ) < p := by
      have := l.2
      simp only [Fin.val_castLE]
      omega
    rw [h1 _ hl]
    rfl
  · intro h
    have hi := i.2
    rw [prod_Iic_eq_prod_castLE G i (p + ((i : ℕ) - p + 1)) (by omega) (by omega),
      Fin.prod_univ_add]
    congr 1
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : ((Fin.castLE (by omega) (Fin.castAdd ((i : ℕ) - p + 1) l) : Fin (p + q)) : ℕ) < p := by
        have := l.2
        simp only [Fin.val_castLE, Fin.val_castAdd]
        omega
      rw [h1 _ hl]
      rfl
    · refine Finset.prod_congr rfl fun l _ => ?_
      have hl : p ≤ ((Fin.castLE (by omega) (Fin.natAdd p l) : Fin (p + q)) : ℕ) := by
        simp only [Fin.val_castLE, Fin.val_natAdd]
        omega
      rw [h2 _ hl]
      congr 1
      ext
      simp

end GlobalTheory.CompanionTheory.Metric.GradedLines
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def nS (a : ℂ) (i : Fin 3) : ℝ := (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)

def wS (a : ℂ) : ℝ := ((1 + ‖a‖ ^ 2) ^ 2)⁻¹

def blk {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun p q : Fin (d + 1) =>
    Fin.cases (Fin.cases e (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => B p' q') q) p

def lin3 (n : Fin 3 → ℝ) : MvPolynomial (Fin 3) ℝ := ∑ i, X i * C (n i)

def lin4 (n : Fin 3 → ℝ) : MvPolynomial (Option (Fin 3)) ℝ := rename some (lin3 n)

def rowW (u : Fin 2 → ℝ) (v : ℝ) : MvPolynomial (Option (Fin 2)) ℝ :=
  C (u 0) * X (some 0) + C (u 1) * X (some 1) + C v * X none

def evalW (n₀ n₁ : Fin 3 → ℝ) : MvPolynomial (Option (Fin 2)) ℝ →ₐ[ℝ] MvPolynomial (Option (Fin 3)) ℝ :=
  aeval fun j => Option.elim j (X none) ![lin4 n₀, lin4 n₁]

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric.FamilyInverse

theorem exists_analytic_family_inverse {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (b₀ : B) (d : B × V → V) (han : AnalyticAt ℂ d (b₀, 0)) (h0 : d (b₀, 0) = 0)
    (hd : HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0)) :
    ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧
      (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  let Φ : B × V → B × V := fun p => (p.1, d p)
  let L : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let L' : (B × V) →L[ℂ] (B × V) :=
    (ContinuousLinearMap.fst ℂ B V).prod ((2⁻¹ : ℂ) • ContinuousLinearMap.snd ℂ B V)
  let Le : (B × V) ≃L[ℂ] (B × V) :=
    ContinuousLinearEquiv.equivOfInverse L L'
      (fun p => by simp [L, L', smul_smul]) (fun p => by simp [L, L', smul_smul])
  have hLe : (Le : (B × V) →L[ℂ] (B × V)) = L := rfl
  have hΦan : AnalyticAt ℂ Φ (b₀, 0) := analyticAt_fst.prod han
  have hΦd : HasFDerivAt Φ L (b₀, 0) := hasFDerivAt_fst.prodMk hd
  have hs : HasStrictFDerivAt Φ (Le : (B × V) →L[ℂ] (B × V)) (b₀, 0) := by
    have := hΦan.hasStrictFDerivAt
    rwa [hΦd.fderiv, ← hLe] at this
  have hfix : Φ (b₀, 0) = (b₀, 0) := by simp [Φ, h0]
  let P := hs.toOpenPartialHomeomorph Φ
  have hPc : (P : B × V → B × V) = Φ := hs.toOpenPartialHomeomorph_coe
  have hPan : AnalyticAt ℂ P.symm (P (b₀, 0)) :=
    P.analyticAt_symm' (i := Le) hs.mem_toOpenPartialHomeomorph_source
      (by rw [hPc]; exact hΦan) (by rw [hPc, hΦd.fderiv, hLe])
  have hΨan : AnalyticAt ℂ P.symm (b₀, 0) := by
    have : P (b₀, 0) = (b₀, 0) := by rw [hPc]; exact hfix
    rwa [this] at hPan
  have hright : ∀ᶠ q in 𝓝 (b₀, 0), Φ (P.symm q) = q := by
    have := hs.eventually_right_inverse
    rw [hfix] at this
    exact this
  have hleft : ∀ᶠ p in 𝓝 (b₀, 0), P.symm (Φ p) = p := hs.eventually_left_inverse
  have hΨ0 : P.symm (b₀, 0) = (b₀, 0) := by
    have := hs.localInverse_apply_image
    rw [hfix] at this
    exact this
  refine ⟨fun q => (P.symm q).2, analyticAt_snd.comp hΨan, by simp [hΨ0], ?_, ?_⟩
  · filter_upwards [hright] with q hq
    have e1 := congrArg Prod.fst hq
    have e2 := congrArg Prod.snd hq
    have h1 : (P.symm q).1 = q.1 := e1
    have h2 : d (P.symm q) = q.2 := e2
    have h3 : (q.1, (P.symm q).2) = P.symm q := by rw [← h1]
    rw [h3, h2]
  · filter_upwards [hleft] with p hp
    have e := congrArg Prod.snd hp
    exact e

end GlobalTheory.CompanionTheory.Metric.FamilyInverse
end

section

namespace GlobalTheory.CompanionTheory.Metric.Rigid

theorem analyticAt_of_comp_immersion {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V)
    (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ) (hψ : AnalyticAt ℂ ψ (F y₀))
    (hker : (fderiv ℂ ψ (F y₀)).ker = ⊥) (hH : AnalyticAt ℂ H y₀) (hF : ContinuousAt F y₀)
    (hEq : ∀ᶠ y in nhds y₀, ψ (F y) = H y) : AnalyticAt ℂ F y₀ := by
  classical
  obtain ⟨P₀, hP₀⟩ := ((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) :
    (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker
  let P : V →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap P₀
  have hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _ := by
    ext1 v
    exact LinearMap.congr_fun hP₀ v
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀) := hψ.differentiableAt.hasFDerivAt
  have hgd : HasFDerivAt (fun x => P (ψ x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀) := by
    have h1 := P.hasFDerivAt.comp (F y₀) hψd
    rw [hPL] at h1
    simpa using h1
  have hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀) := (P.analyticAt _).comp hψ
  have hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀) := hga.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hφa := (hgc.to_localInverse hgd hn).analyticAt
  have hleft := (hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  have hH0 : ψ (F y₀) = H y₀ := hEq.self_of_nhds
  have hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F := by
    filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2
    rw [← h2]
    exact h1
  have hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀ := by
    have h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀)) := by
      rw [← hH0]
      exact hφa
    have hPH : AnalyticAt ℂ (fun y => P (H y)) y₀ := (P.analyticAt (H y₀)).comp hH
    exact h0.comp_of_eq hPH rfl
  exact hcomp.congr hev

end GlobalTheory.CompanionTheory.Metric.Rigid
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcHolo_det_differentiableAt {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Fintype n] [DecidableEq n] (M : E → Matrix n n ℂ) (x : E)
    (h : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) x) :
    DifferentiableAt ℂ (fun b => (M b).det) x := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ s : Finset n, DifferentiableAt ℂ (fun b => ∏ i ∈ s, M b (σ i) i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h _ _).fun_mul ih
  exact key _

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Metric

theorem norm_le_mul_norm_div_of_bounded_on_ball {V W : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {ψ : V → W} {R M : ℝ}
    (hd : DifferentiableOn ℂ ψ (ball (0 : V) R)) (h0 : ψ 0 = 0)
    (hM : ∀ x ∈ ball (0 : V) R, ‖ψ x‖ ≤ M) {x : V} (hx : x ∈ ball (0 : V) R) :
    ‖ψ x‖ ≤ M * ‖x‖ / R := by
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (R₂ := M) hd (by
    intro y hy
    rw [mem_closedBall, h0, dist_zero_right]
    exact hM y hy) hx
  rw [h0, dist_zero_right, dist_zero_right] at h
  calc ‖ψ x‖ ≤ M / R * ‖x‖ := h
    _ = M * ‖x‖ / R := by ring

theorem norm_le_of_vanishing_on_axes {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (b₀ : B) (G : B × V × V → W) (R : ℝ) (hR : 0 < R)
    (hG : DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R))
    (hb : ∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1)
    (hz : ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) :
    ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R,
      ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  intro b hbm s hs t ht

  have h1 : ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ / R := by
    intro s hs t ht
    have hd : DifferentiableOn ℂ (fun s' => G (b, s', t)) (ball (0 : V) R) :=
      hG.comp ((differentiableOn_const b).prodMk (differentiableOn_id.prodMk (differentiableOn_const t)))
        (by intro s' hs'; exact ⟨hbm, hs', ht⟩)
    have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm t ht).2
      (fun s' hs' => hb _ ⟨hbm, hs', ht⟩) hs
    rwa [one_mul] at h

  have hd : DifferentiableOn ℂ (fun t' => G (b, s, t')) (ball (0 : V) R) :=
    hG.comp ((differentiableOn_const b).prodMk ((differentiableOn_const s).prodMk differentiableOn_id))
      (by intro t' ht'; exact ⟨hbm, hs, ht'⟩)
  have h := norm_le_mul_norm_div_of_bounded_on_ball hd (hz b hbm s hs).1
    (fun t' ht' => h1 s hs t' ht') ht
  calc ‖G (b, s, t)‖ ≤ ‖s‖ / R * ‖t‖ / R := h
    _ = ‖s‖ * ‖t‖ / R ^ 2 := by ring

end GlobalTheory.CompanionTheory.Metric
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

open MeasureTheory Real

def punct {n : ℕ} (R : ℝ) : Set (Fin n → ℂ) := {z | ∀ i, z i ≠ 0 ∧ ‖z i‖ < R}

def pker (ρ : ℝ) (w : ℂ) (t : ℝ) : ℝ := poissonKernel 0 w (circleMap 0 ρ t)

def angMeas : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

instance : IsProbabilityMeasure angMeas := ⟨by
  have h : (0 : ℝ) < 2 * π := by positivity
  simp only [angMeas, Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]⟩

theorem integral_angMeas (F : ℂ → ℝ) (ρ : ℝ) :
    ∫ t, F (circleMap 0 ρ t) ∂angMeas = Real.circleAverage F 0 ρ := by
  have h : (0 : ℝ) < 2 * π := by positivity
  rw [angMeas, integral_smul_measure, Real.circleAverage_def,
    intervalIntegral.integral_of_le h.le, ENNReal.toReal_ofReal (by positivity)]

def torusPt {n : ℕ} (ρ : ℝ) (θ : Fin n → ℝ) : Fin n → ℂ := fun i => circleMap 0 ρ (θ i)

def polyPoisson {n : ℕ} (ρ : ℝ) (h : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)

def SepHarm {n : ℕ} (R : ℝ) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∀ z ∈ punct R, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => f (Function.update z i t)) (z i)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

end

section

@[expose] public section

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.analytic_doubling_map_local_inverse : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (d : B × V → V), AnalyticAt ℂ d (b₀, 0) → d (b₀, 0) = 0 → HasFDerivAt d ((2 : ℂ) • ContinuousLinearMap.snd ℂ B V) (b₀, 0) → ∃ h : B × V → V, AnalyticAt ℂ h (b₀, 0) ∧ h (b₀, 0) = 0 ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), d (p.1, h p) = p.2) ∧ (∀ᶠ p : B × V in 𝓝 (b₀, 0), h (p.1, d p) = p.2) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | exact GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse | (intros; apply GlobalTheory.CompanionTheory.Metric.FamilyInverse.exists_analytic_family_inverse <;> assumption)

end
end
