module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LocalToGlobal.Columns.PolyFn
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle127
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle126
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory.Branching.Family

variable {ι : Type} [Fintype ι]


omit [Fintype ι] in
theorem exists_poly_blockAct_coef {k : ℕ} (f : MvPolynomial (ι × Fin k × Fin k) ℂ)
    (l : Module.Dual ℂ (MvPolynomial (ι × Fin k × Fin k) ℂ)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → Matrix (Fin k) (Fin k) ℂ,
      l (Formalism.GradedWeylDivisibility.blockAct ℂ g f) = eval (fun x => g x.1 x.2.1 x.2.2) P := by
  classical

  let Φ : ι × Fin k × Fin k → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun v => ∑ b : Fin k, C (X (v.1, v.2.1, b) : MvPolynomial (ι × Fin k × Fin k) ℂ) * X (v.1, (b, v.2.2))
  let T : MvPolynomial (ι × Fin k × Fin k) ℂ → MvPolynomial (ι × Fin k × Fin k) (MvPolynomial (ι × Fin k × Fin k) ℂ) :=
    fun p => aeval Φ (map (C : ℂ →+* MvPolynomial (ι × Fin k × Fin k) ℂ) p)
  have hT : ∀ (g : ι → Matrix (Fin k) (Fin k) ℂ) (p : MvPolynomial (ι × Fin k × Fin k) ℂ),
      Formalism.GradedWeylDivisibility.blockAct ℂ g p = map (eval fun x => g x.1 x.2.1 x.2.2) (T p) := by
    intro g p
    induction p using MvPolynomial.induction_on with
    | C a => simp [T, aeval_C, MvPolynomial.algebraMap_eq, map_C, eval_C]
    | add p q hp hq => simp only [map_add (f := _), hp, hq, T]
    | mul_X p v hp =>
      simp only [T] at hp ⊢
      simp only [map_mul, hp]
      congr 1

      simp only [Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_X, Φ, map_sum, map_mul, map_C, eval_X]
  refine ⟨∑ m ∈ (T f).support, C (l (monomial m 1)) * (T f).coeff m, fun g => ?_⟩
  rw [hT g f]
  conv_lhs => rw [(T f).as_sum]

  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_monomial, map_mul, eval_C]
  rw [show (monomial m (eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m)) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      eval (fun x => g x.1 x.2.1 x.2.2) ((T f).coeff m) • monomial m 1 by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul, mul_comm]

theorem exists_coef_rhoK {k : ℕ} (lam : ι → DomWeight k) (f : VV ℂ lam) (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin k × Fin k) ℂ, ∀ g : ι → GL (Fin k) ℂ,
      l (rhoK lam g f) = (∏ τ, (g τ : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift) *
        eval (fun x => (g x.1 : Matrix (Fin k) (Fin k) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (K := ℂ) (p := VV ℂ lam) l
  obtain ⟨P, hP⟩ := exists_poly_blockAct_coef (ι := ι) (k := k) (f : MvPolynomial (ι × Fin k × Fin k) ℂ) L
  refine ⟨rename (fun x : ι × Fin k × Fin k => (x.1, x.2.2, x.2.1)) P, fun g => ?_⟩
  have hl : l (rhoK lam g f) = L ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) := by
    rw [← hL]; rfl
  have hv : ((rhoK lam g f : VV ℂ lam) : MvPolynomial (ι × Fin k × Fin k) ℂ) =
      detTwK lam g • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.transpose ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ))
        (f : MvPolynomial (ι × Fin k × Fin k) ℂ) := rfl
  have hd : detTwK lam g = ∏ τ, ((g τ : GL (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ).det ^ (lam τ).detShift := by
    simp only [detTwK, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [hl, hv, map_smul, hP, eval_rename, smul_eq_mul, hd]
  rfl

theorem det_diag_one {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g : Matrix (Fin N) (Fin N) ℂ).det = (g : Matrix (Fin n) (Fin n) ℂ).det := by
  subst h
  have h1 : ∀ a b : Fin n, ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) a.castSucc b.castSucc = (g : Matrix (Fin n) (Fin n) ℂ) a b := by
    intro a b
    simp [GlobalTheory.Branching.embGL_apply]
  have h2 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.Branching.embGL_apply]
  have hev : (-1 : ℂ) ^ (n + n) = 1 := Even.neg_one_pow ⟨n, rfl⟩
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · simp only [h2, Fin.succAbove_last, Fin.val_last, hev, one_mul, mul_one]
    congr 1
    ext a b
    exact h1 a b
  · intro j _ hj
    have h3 : ((Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n (n + 1) rfl g : GL (Fin (n + 1)) ℂ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) j = 0 := by
      simp [GlobalTheory.Branching.embGL_apply, Ne.symm hj]
    rw [h3, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem exists_coef_rhoK_emb {n N : ℕ} (h : n + 1 = N) (lam : ι → DomWeight N) (f : VV ℂ lam)
    (l : Module.Dual ℂ (VV ℂ lam)) :
    ∃ P : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ g : ι → GL (Fin n) ℂ,
      l (rhoK lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h (g τ)) f) =
        (∏ τ, (g τ : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift) *
          eval (fun x => (g x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) P := by
  classical
  obtain ⟨P, hP⟩ := exists_coef_rhoK lam f l

  let S : ι × Fin N × Fin N → MvPolynomial (ι × Fin n × Fin n) ℂ := fun x =>
    if hab : x.2.1.val < n ∧ x.2.2.val < n then X (x.1, ⟨x.2.1.val, hab.1⟩, ⟨x.2.2.val, hab.2⟩)
    else if x.2.1 = x.2.2 then 1 else 0
  refine ⟨aeval S P, fun g => ?_⟩
  rw [hP, Formalism.L2.Col.eval_aeval_poly]
  simp only [det_diag_one]
  congr 1
  apply congrArg (fun F => eval F P)
  funext x
  simp only [S, GlobalTheory.Branching.embGL_apply]
  split_ifs <;> simp

theorem prod_zpow_mul_eq_iff (d : ι → ℂ) (x y : ℂ) (hd : ∀ τ, d τ ≠ 0) (a b : ι → ℤ) :
    (∏ τ, d τ ^ a τ) * x = (∏ τ, d τ ^ b τ) * y ↔
      (∏ τ, d τ ^ (a τ - b τ).toNat) * x = (∏ τ, d τ ^ (b τ - a τ).toNat) * y := by

  have split : ∀ (c e : ι → ℤ) τ, d τ ^ c τ = d τ ^ min (c τ) (e τ) * d τ ^ (c τ - e τ).toNat := by
    intro c e τ
    rw [← zpow_natCast, ← zpow_add₀ (hd τ)]
    congr 1
    rcases le_total (c τ) (e τ) with h | h
    · have h' : c τ - e τ ≤ 0 := by linarith
      rw [min_eq_left h, Int.toNat_of_nonpos h', Nat.cast_zero, add_zero]
    · have h' : 0 ≤ c τ - e τ := by linarith
      rw [min_eq_right h, Int.toNat_of_nonneg h']
      ring
  have hne : (∏ τ, d τ ^ min (a τ) (b τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hd τ)
  have hmin : ∀ τ, min (b τ) (a τ) = min (a τ) (b τ) := fun τ => min_comm _ _
  rw [Finset.prod_congr rfl fun τ _ => split a b τ, Finset.prod_congr rfl fun τ _ => split b a τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [hmin]
  rw [mul_assoc, mul_assoc, mul_right_inj' hne]

theorem equivariant_gl_of_unitary {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n)
    (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) =
        rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v))
    (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ) :
    φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  classical
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro l
  rw [map_sub, sub_eq_zero]
  obtain ⟨P₁, hP₁⟩ := exists_coef_rhoK_emb hN.symm Λ v (l ∘ₗ φ)
  obtain ⟨P₂, hP₂⟩ := exists_coef_rhoK σ (φ v) l

  let D : ι → MvPolynomial (ι × Fin n × Fin n) ℂ := fun τ =>
    (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hD : ∀ (y : ι → Matrix (Fin n) (Fin n) ℂ) τ, eval (fun x => y x.1 x.2.1 x.2.2) (D τ) = (y τ).det := by
    intro y τ
    simp only [D]
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [RingHom.mapMatrix_apply]
  let a : ι → ℤ := fun τ => (Λ τ).detShift
  let b : ι → ℤ := fun τ => (σ τ).detShift

  let Q := (∏ τ, D τ ^ (a τ - b τ).toNat) * P₁ - (∏ τ, D τ ^ (b τ - a τ).toNat) * P₂
  have hQ : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, eval (fun x => y x.1 x.2.1 x.2.2) Q =
      (∏ τ, (y τ).det ^ (a τ - b τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₁ -
        (∏ τ, (y τ).det ^ (b τ - a τ).toNat) * eval (fun x => y x.1 x.2.1 x.2.2) P₂ := by
    intro y
    simp only [Q, map_sub, map_mul, map_prod, map_pow, hD]

  have hQ0 : Q = 0 := by
    refine Formalism.L2.Col.eq_zero_of_forall_unitary (fun _ => 1) (fun _ => by simp) Q fun u hu => ?_
    simp only [one_mul]
    let w : ι → Matrix.unitaryGroup (Fin n) ℂ := fun τ =>
      ⟨u τ, Matrix.mem_unitaryGroup_iff'.mpr (by simpa [Matrix.star_eq_conjTranspose] using hu τ)⟩
    have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have e := congrArg l (hφ w v)
    have e₁ := hP₁ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    have e₂ := hP₂ (fun τ => GlobalTheory.Branching.unitaryIncl n (w τ))
    simp only [LinearMap.comp_apply] at e₁
    rw [e₁, e₂] at e
    simp only [GlobalTheory.Branching.unitaryIncl_coe] at e
    rw [hQ u, sub_eq_zero]
    exact (prod_zpow_mul_eq_iff (fun τ => (u τ).det) _ _ hdet a b).mp e
  have hg : ∀ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := fun τ =>
    by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have e₃ := hQ (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ))
  rw [hQ0, map_zero, eq_comm, sub_eq_zero] at e₃
  have e₁ := hP₁ g
  simp only [LinearMap.comp_apply] at e₁
  rw [e₁, hP₂ g]
  exact (prod_zpow_mul_eq_iff (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det) _ _ hg a b).mpr e₃

end GlobalTheory.Branching.Family
end

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

theorem _root_.GlobalTheory.T.subsingleton_borelJacquet_of_cuspidal_segment_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (l d : ℕ), 0 < l → 1 < d → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin d) k) W) (π : Representation ℂ (GL (Fin (l * d)) k) V), IsCuspidal σ → (∀ e : (Σ _ : Fin l, Fin d) ≃ Fin (l * d), Nonempty ((jac e π).Equiv (piTensor (segTerm σ l)))) → Subsingleton (Jacquet π (unipB k (Fin (l * d)))) := by
  first | exact @GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | exact GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB | (intros; apply GlobalTheory.SmGL.CuspSegment.subsingleton_jacquet_unipB <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.FockTensor

theorem derived_adjoint_and_casimir (p q : ℕ) (T : GrpData p q) (πU : URep T) (V₁ V₂ : Type)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ V₁) (a₂ : Mat p q →ₗ[ℂ] Module.End ℂ V₂)
    (E₁ : V₁ →ₗ[ℂ] πU.H) (E₂ : V₂ →ₗ[ℂ] πU.H)
    (h₁ : ∀ Y ∈ upq p q, ∀ x,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₁ x)) (E₁ (a₁ Y x)) 0)
    (h₂ : ∀ Y ∈ upq p q, ∀ y,
      HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (E₂ y)) (E₂ (a₂ Y y)) 0) :
    (∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y))) ∧
      ∀ x y, inner ℂ (E₁ (casimir a₁ x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (casimir a₂ y)) := by
  have hreal : ∀ Y ∈ upq p q, ∀ x y,
      inner ℂ (E₁ (a₁ Y x)) (E₂ y) = - inner ℂ (E₁ x) (E₂ (a₂ Y y)) := by
    intro Y hY x y
    have h := (h₁ Y hY x).inner ℂ (h₂ Y hY y)
    simp only [inner_pi_pi] at h
    have h0 := h.unique (hasDerivAt_const (0 : ℝ) _)
    simp only [zero_smul, T.expt_zero, map_one, ContinuousLinearMap.one_apply] at h0
    linear_combination h0
  have hZ : ∀ Z x y, inner ℂ (E₁ (a₁ Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (a₂ (adjZ Z) y)) := by
    intro Z x y
    obtain ⟨X, hX, Y, hY, rfl⟩ := exists_upq_add Z
    rw [adjZ_add, adjZ_smul, (mem_upq_iff X).1 hX, (mem_upq_iff Y).1 hY]
    simp only [map_add (f := _), map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.neg_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      inner_neg_right, hreal X hX, hreal Y hY]
    rfl
  refine ⟨hZ, fun x y => ?_⟩

  simp only [casimir, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, Module.End.mul_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hZ, hZ, adjZ_Eab, adjZ_Eab]
  simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
  linear_combination (sgnIx b * sgnIx b * inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y)))) *
    sgnIx_mul_self a + inner ℂ (E₁ x) (E₂ (a₂ (Eab a b) (a₂ (Eab b a) y))) * sgnIx_mul_self b

end GlobalTheory.FockTensor
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoords

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem trace_tmul_base {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (r : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] x) = r * algebraMap F R (Algebra.trace F E x) := by
  have h1 : (r ⊗ₜ[F] x : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] x) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem repr_eq_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (x : E) (l : ι) :
    Algebra.trace F E
        ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l * x) = b.repr x l := by
  have h := congrArg (Algebra.traceForm F E
      ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l)) (b.sum_repr x)

  rw [map_sum] at h
  simp only [map_smul, LinearMap.BilinForm.apply_dualBasis_left, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Algebra.traceForm_apply] at h
  exact h.symm

theorem coords_gen (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ (d : ℕ) (c e : Fin d → E), ∀ w : AF F ⊗[F] E,
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w =
        ∑ l, sndA F (Algebra.trace (AF F) (AF F ⊗[F] E) (((1 : AF F) ⊗ₜ[F] c l) * w)) ⊗ₜ[F] e l := by
  classical
  let b := Module.finBasis F E
  refine ⟨_, fun l => (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b l, b, ?_⟩
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_tmul_base, map_mul,
      AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    simp only [repr_eq_trace]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, ← Finset.sum_add_distrib, TensorProduct.add_tmul]

end GlobalTheory.TwistCoords

namespace GlobalTheory.TwistCoords

theorem finPart_eq_sum_trace :
    ∀ (D : D7), ∃ (d : ℕ) (c e : Fin d → D.host.E), ∀ w : AE D, finPart D w =
      ∑ l, sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c l) * w)) ⊗ₜ[D.host.F] e l := by
  intro D
  obtain ⟨d, c, e, h⟩ := coords_gen D.host.F D.host.E
  exact ⟨d, c, e, fun w => h w⟩

end GlobalTheory.TwistCoords
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteLiftZfin

open Matrix

theorem isCuspFun_of_posDef {D : D7} {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) (φ : GA D V → ℂ) :
    IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hτ : ∀ a, tauE D τ0 (star a) = starRingEnd ℂ (tauE D τ0 a) := D.sp.cm.cmUnram.2.1 (tauE D τ0)
  have h1 := congrArg (tauE D τ0) (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have hx : star (fun i => tauE D τ0 (C i ⟨0, hr⟩)) ⬝ᵥ (gramAt D V τ0 *ᵥ fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]

    simp only [gramAt, Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm
  have h2 : (fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    by_contra hne
    have := (hV τ0).dotProduct_mulVec_pos hne
    rw [hx] at this
    exact lt_irrefl _ this
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact (tauE D τ0).injective ((congrFun h2 i).trans (map_zero (tauE D τ0)).symm)

end GlobalTheory.DefiniteLiftZfin
end
end
