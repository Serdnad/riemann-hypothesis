module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle289
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.wExp_h : ExpBasic → SqExp → TorFacts → WExp := by
  intro hB hS hT E _ _ _ a τ W
  classical
  obtain ⟨-, -, hmono, -, -, hinv⟩ := hB
  set v₀ := InfinitePlace.mk τ with hv₀
  let d : ℕ := ∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs
  have hps : ∀ k, psum (W v₀) k ≤ d := fun k => by
    have h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ) :=
      (Finset.sum_le_sum fun i _ => Int.le_natAbs).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)
    have h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [d, Nat.cast_add, Nat.cast_sum]
    omega
  have h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d) := fun k w L =>
    ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩
  refine ⟨d, fun k x hx v L => ?_⟩
  have h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ),
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d) := by
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · rw [hv₀, e]
      refine ⟨fun z => (hx z).1, fun w L => ?_⟩
      simp only [(hx _).2]
      exact h1 k w L
    · rw [hv₀, e]
      refine ⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩
      have e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹ := fun z => by
        rw [← (hT a k z).2.2.2, ← (hx z).2]
        ext i j
        simp [cEmb, GlobalTheory.DefiniteBC.coord_conjugate]
      simp only [e2]
      have h3 := (hinv _ _).2 (h1 k w L).2
      rw [neg_neg] at h3
      exact ⟨h3, (hinv _ _).1 (h1 k w L).1⟩
  let Φ : W.Sp →ₗ[ℂ] (Circle → ℂ) := LinearMap.pi fun z => L ∘ₗ W.rep (x z)
  let N : Submodule ℂ W.Sp := (ExpLe d ⊓ ExpGe (-d)).comap Φ
  have hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N := fun e => by
    have h := h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
    have e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
        (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀)) := by
      funext z
      have := rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)
      rw [Function.update_eq_self] at this
      exact congrArg L this
    change Φ _ ∈ ExpLe d ⊓ ExpGe (-d)
    rw [e3]
    exact h
  have h0 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0)
    (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)
  exact (Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial

private theorem zp {k : Type} [NormedField k] [IsUltrametricDist k] {u : k} {ε : ℝ} (h0 : 0 ≤ ε) (hu : ‖u‖ = 1) (h : ‖u - 1‖ ≤ ε)
    (n : ℤ) : ‖u ^ n - 1‖ ≤ ε := by
  have hu0 : u ≠ 0 := fun e => by simp [e] at hu
  have step : ∀ w x : k, ‖w‖ = 1 → ‖w - 1‖ ≤ ε → ‖x - 1‖ ≤ ε → ‖x * w - 1‖ ≤ ε := fun w x hw h1 h2 => by
    rw [show x * w - 1 = (x - 1) * w + (w - 1) by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rwa [norm_mul, hw, mul_one]
  induction n using Int.induction_on with
  | zero => simpa using h0
  | succ n ih => rw [zpow_add_one₀ hu0]; exact step _ _ hu h ih
  | pred n ih =>
    rw [zpow_sub_one₀ hu0]
    refine step _ _ (by rw [norm_inv, hu, inv_one]) ?_ ih
    rw [show u⁻¹ - 1 = -(u⁻¹ * (u - 1)) by field_simp; ring, norm_neg, norm_mul, norm_inv, hu, inv_one, one_mul]
    exact h

theorem UpperTheory.Gal.Wt.deltaNear_h : DeltaNear := by
  intro l _ ι a ν h hI
  let m : GL (Fin a) ℂ → Fin a × Fin a → Qbar l := fun g p => ι.symm ((g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1)
  let D : MvPolynomial (Fin a × Fin a) ℤ := (Matrix.of fun i j => (X (j, i) : MvPolynomial (Fin a × Fin a) ℤ)).det
  have hmap : ∀ (w : Fin a × Fin a → ℂ) (P : MvPolynomial (Fin a × Fin a) ℤ),
      ι.symm (aeval w P) = aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  have hD : ∀ g : GL (Fin a) ℂ, ι.symm (g : Matrix (Fin a) (Fin a) ℂ).det = aeval (m g) D := fun g => by
    rw [← hmap, AlgHom.map_det]
    congr 2
    ext i j
    simp
  have hδ : ∀ g : GL (Fin a) ℂ, ι.symm (delta ν g) = (aeval (m g) D) ^ ν.detShift * aeval (m g) (extremal ℤ a ν) := fun g => by
    have e1 : (aeval fun p : Fin a × Fin a => (1 : Matrix (Fin a) (Fin a) ℂ) p.1 p.2).comp
        (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (g : Matrix (Fin a) (Fin a) ℂ).transpose) =
        aeval fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1 :=
      MvPolynomial.algHom_ext fun v => by simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.one_apply]
    have e2 : delta ν g = (g : Matrix (Fin a) (Fin a) ℂ).det ^ ν.detShift *
        aeval (fun p : Fin a × Fin a => (g : Matrix (Fin a) (Fin a) ℂ) p.2 p.1) (extremal ℤ a ν) := by
      change aeval _ (sqAct ℂ a ν g (extremal ℂ a ν)) = _
      rw [sqAct, map_smul, ← AlgHom.comp_apply, e1, detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply,
        ← Formalism.L2.DIV.map_extremal (algebraMap ℤ ℂ), aeval_map_algebraMap, smul_eq_mul]
    rw [e2, map_mul, map_zpow₀, hD, hmap]
  have hm : ∀ p, ‖m h p‖ ≤ 1 := fun p => (hI _ _).1
  have hb : ∀ (x : Fin a × Fin a → Qbar l), (∀ p, ‖x p‖ ≤ 1) → ∀ P : MvPolynomial (Fin a × Fin a) ℤ, ‖aeval x P‖ ≤ 1 :=
    fun x hx P => (aeval_sub_le le_rfl hx hx (fun _ => by simp) P).1
  have hd1 : ‖aeval (m h) D‖ = 1 := by
    have h1 := hb _ hm D
    have h2 := hb (m h⁻¹) (fun p => (hI _ _).2) D
    have h3 : ‖aeval (m h) D‖ * ‖aeval (m h⁻¹) D‖ = 1 := by
      rw [← norm_mul, ← hD, ← hD, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, norm_one]
    nlinarith [norm_nonneg (aeval (m h) D), norm_nonneg (aeval (m h⁻¹) D)]
  refine ⟨by rw [hδ, norm_mul, norm_zpow, hd1, one_zpow, one_mul]; exact hb _ hm _, fun ε hε hN => ?_⟩
  have h1 : ∀ p, ‖m 1 p‖ ≤ 1 := fun p => by
    simp only [m, Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  have hc : ∀ p, ‖m h p - m 1 p‖ ≤ ε := fun p => by
    have := hN p.2 p.1
    rwa [map_sub] at this
  have eD : aeval (m 1) D = 1 := by rw [← hD]; simp
  have eE : aeval (m 1) (extremal ℤ a ν) = 1 := by
    rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
    refine Finset.prod_eq_one fun s _ => ?_
    rw [map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det]
    rw [show ∀ M : Matrix (Fin (s.val + 1)) (Fin (s.val + 1)) (Qbar l), M = 1 → M.det ^ (ν.natW s - Formalism.GradedWeylDivisibility.nuNext ν.natW s) = 1 from
      fun M hM => by rw [hM, Matrix.det_one, one_pow]]
    ext i j
    simp [m, Matrix.one_apply, eq_comm]
  have c1 : ‖aeval (m h) D - 1‖ ≤ ε := by rw [← eD]; exact (aeval_sub_le hε hm h1 hc D).2.2
  have c2 : ‖aeval (m h) (extremal ℤ a ν) - 1‖ ≤ ε := by rw [← eE]; exact (aeval_sub_le hε hm h1 hc (extremal ℤ a ν)).2.2
  rw [map_sub, map_one, hδ, show ∀ x y : Qbar l, x * y - 1 = x * (y - 1) + (x - 1) from fun x y => by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (zp hε hd1 c1 _))
  rwa [norm_mul, norm_zpow, hd1, one_zpow, one_mul]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_entry_mem_expLe_one_expGe_zero (h : ExpBasic) (a k : ℕ) (A B : GL (Fin a) ℂ) (i j : Fin a) :
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpLe 1 ∧
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpGe 0 := by
  obtain ⟨_, _, hmono, hmon, hconst, _⟩ := h
  have heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l *
        ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j) := by
    funext z
    rw [Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]
    simp [tor_coe, Matrix.diagonal_mul]
  rw [heq]
  constructor
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hmono 0 1 (by norm_num)).1
        (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1
      funext z
      simp [hl]
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmono 0 1 (by norm_num)).2
        (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1
      funext z
      simp [hl]

private theorem pow_mem_expLe_expGe_of_mem (h : ExpBasic) (f : Circle → ℂ) (hf : f ∈ ExpLe 1 ∧ f ∈ ExpGe 0) (n : ℕ) :
    (fun z => f z ^ n) ∈ ExpLe (n : ℤ) ∧ (fun z => f z ^ n) ∈ ExpGe 0 := by
  obtain ⟨hmulL, hmulG, _, _, hconst, _⟩ := h
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact hconst 1
  | succ n ih =>
    have e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z := by
      funext z
      exact pow_succ _ _
    rw [e]
    constructor
    · have := hmulL _ _ _ _ ih.1 hf.1
      push_cast
      exact this
    · have := hmulG _ _ _ _ ih.2 hf.2
      simpa using this

private theorem prod_pow_mem_expLe_sum_expGe {ι : Type} [DecidableEq ι] (h : ExpBasic) (e : ι → Circle → ℂ)
    (he : ∀ i, e i ∈ ExpLe 1 ∧ e i ∈ ExpGe 0) (d : ι → ℕ) (S : Finset ι) :
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpLe ((∑ i ∈ S, d i : ℕ) : ℤ) ∧
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpGe 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]
    exact h.2.2.2.2.1 1
  | insert x S hx ih =>
    have hp := pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)
    have e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) =
        fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z := by
      funext z
      exact Finset.prod_insert hx
    rw [e1]
    constructor
    · have := h.1 _ _ _ _ hp.1 ih.1
      rw [Finset.sum_insert hx, Nat.cast_add]
      exact this
    · have := h.2.1 _ _ _ _ hp.2 ih.2
      simpa using this

theorem UpperTheory.Gal.Wt.pevExp_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.PevExp := by
  intro h a k P A B
  classical
  let e : Fin a × Fin a → Circle → ℂ := fun p z =>
    ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2
  have he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0 := fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2
  have hsum : (fun z => pev P (A * (tor a k z * B))) =
      ∑ d ∈ P.support, fun z => AddMonoidAlgebra.coeff P d * ∏ i ∈ d.support, e i z ^ d i := by
    funext z
    rw [Finset.sum_apply]
    simp only [pev]
    rw [MvPolynomial.eval_eq]
  rw [hsum]
  constructor
  · refine Submodule.sum_mem _ fun d hd => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).1
    have hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ) := by
      exact_mod_cast MvPolynomial.le_totalDegree hd
    have hm := (h.2.2.1 _ _ hle).1 hp
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hm using 1
  · refine Submodule.sum_mem _ fun d _ => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).2
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hp using 1
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt
open MvPolynomial


private theorem coeff_diag {a : ℕ} (t : Fin a → ℂ) (f : MvPolynomial (Fin a × Fin a) ℂ) (m : Fin a × Fin a →₀ ℕ) :
    AddMonoidAlgebra.coeff (Formalism.GradedWeylDivisibility.rowAct ℂ (n := a) (Matrix.diagonal t) f) m = (∏ v : Fin a × Fin a, t v.1 ^ m v) * AddMonoidAlgebra.coeff f m := by
  have hg : (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2))
      = fun v => MvPolynomial.C (t v.1) * MvPolynomial.X v := by
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.diagonal_apply_ne t (Ne.symm hb), map_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  show AddMonoidAlgebra.coeff (MvPolynomial.aeval
      (fun v : Fin a × Fin a => ∑ b, MvPolynomial.C (Matrix.diagonal t v.1 b) * MvPolynomial.X (b, v.2)) f) m = _
  rw [hg]
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [aeval_monomial, MvPolynomial.algebraMap_eq, Finsupp.prod]
    simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [MvPolynomial.prod_X_pow_eq_monomial, ← mul_assoc, ← map_mul, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      rw [mul_one, mul_comm]
      congr 1
      refine Finset.prod_subset (Finset.subset_univ _) ?_
      intro v _ hv
      simp only [Finsupp.mem_support_iff, not_not] at hv
      rw [hv, pow_zero]
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem UpperTheory.Gal.Wt.sqExp_h : ExpBasic → EvLem → Dom → SqExp := by
  intro hE hEv hDom a k κ w L
  obtain ⟨_, _, hle, hmon, _, _⟩ := hE
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = (Finset.univ.filter fun i : Fin a => (i : ℕ) < k).card := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin a × Fin a →₀ ℕ) → ℕ,
      e = fun m => ∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), Formalism.GradedWeylDivisibility.rowDeg m i := ⟨_, rfl⟩
  have hdet : ∀ z : Circle, detPow ℂ a (tor a k z) κ.detShift = (z : ℂ) ^ ((D : ℤ) * κ.detShift) := by
    intro z
    simp only [detPow]
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, tor_coe, Matrix.det_diagonal,
      ← Finset.prod_filter, Finset.prod_const, zpow_mul, zpow_natCast, hD]
  have hprod : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      (∏ v : Fin a × Fin a, (if ((v.1 : Fin a) : ℕ) < k then (z : ℂ) else 1) ^ m v) = (z : ℂ) ^ e m := by
    intro z m
    have hin : ∀ i : Fin a, (∏ s : Fin a, (if (i : ℕ) < k then (z : ℂ) else 1) ^ m (i, s))
        = if (i : ℕ) < k then (z : ℂ) ^ Formalism.GradedWeylDivisibility.rowDeg m i else 1 := by
      intro i
      split_ifs
      · rw [Finset.prod_pow_eq_pow_sum]
        rfl
      · simp
    rw [Fintype.prod_prod_type]
    dsimp only
    simp only [hin]
    rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum, he]
  have hcoeff : ∀ (z : Circle) (m : Fin a × Fin a →₀ ℕ),
      AddMonoidAlgebra.coeff ((sqRep ℂ a κ (tor a k z) w : nablaSq ℂ a κ) : MvPolynomial (Fin a × Fin a) ℂ) m
        = AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) m
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e m : ℤ)) := by
    intro z m
    show AddMonoidAlgebra.coeff (sqAct ℂ a κ (tor a k z) (w : MvPolynomial (Fin a × Fin a) ℂ)) m = _
    rw [sqAct, MvPolynomial.coeff_smul, hdet, tor_coe, Matrix.diagonal_transpose, coeff_diag]
    beta_reduce
    rw [hprod, smul_eq_mul, zpow_add₀ (Circle.coe_ne_zero z), zpow_natCast]
    ring
  let ev : (Fin a × Fin a →₀ ℕ) → nablaSq ℂ a κ →ₗ[ℂ] ℂ :=
    fun x => (MvPolynomial.lcoeff ℂ x).comp (nablaSq ℂ a κ).subtype
  have hsep : ∀ p : nablaSq ℂ a κ, (∀ x, ev x p = 0) → p = 0 := by
    intro p hp
    apply Subtype.ext
    ext x
    simpa [ev] using hp x
  have hterm : ∀ T : Submodule ℂ (Circle → ℂ),
      (∀ x, AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x ≠ 0 →
        (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) ∈ T) →
      (fun z => L (sqRep ℂ a κ (tor a k z) w)) ∈ T := by
    intro T hT
    refine hEv (nablaSq ℂ a κ) (Fin a × Fin a →₀ ℕ) Circle ev hsep T (fun z => sqRep ℂ a κ (tor a k z) w) ?_ L
    intro x
    have hfun : (fun z => ev x (sqRep ℂ a κ (tor a k z) w))
        = fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ)) := funext fun z => hcoeff z x
    rw [hfun]
    by_cases hx : AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x = 0
    · have h0 : (fun z : Circle => AddMonoidAlgebra.coeff (w : MvPolynomial (Fin a × Fin a) ℂ) x
          * (z : ℂ) ^ ((D : ℤ) * κ.detShift + (e x : ℤ))) = 0 := by
        funext z
        simp [hx]
      rw [h0]
      exact T.zero_mem
    · exact hT x hx
  have hds : ∀ i : Fin a, κ.detShift ≤ κ.w i := by
    intro i
    simp only [DomWeight.detShift, dif_pos (Fin.pos i)]
    exact κ.anti (Fin.le_iff_val_le_val.mpr (by simp only; omega))
  have hnat : ∀ i : Fin a, ((κ.natW i : ℕ) : ℤ) = κ.w i - κ.detShift :=
    fun i => Int.toNat_of_nonneg (sub_nonneg.mpr (hds i))
  have hDa : D ≤ a := by
    rw [hD]
    exact (Finset.card_filter_le _ _).trans (Finset.card_fin a).le
  refine ⟨hterm _ fun x hx => ?_, hterm _ fun x _ => ?_⟩
  · have hxs : x ∈ (w : MvPolynomial (Fin a × Fin a) ℂ).support := MvPolynomial.mem_support_iff.mpr hx
    have hbound := hDom a κ _ w.2 x hxs k
    have hup : (D : ℤ) * κ.detShift + (e x : ℤ) ≤ psum κ k := by
      have h1 : (e x : ℤ) ≤ ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) := by
        rw [he]
        exact_mod_cast hbound
      have h2 : (D : ℤ) * κ.detShift
          + ((∑ i ∈ Finset.univ.filter (fun i : Fin a => (i : ℕ) < k), κ.natW i : ℕ) : ℤ) = psum κ k := by
        rw [Nat.cast_sum]
        simp only [hnat]
        rw [Finset.sum_sub_distrib, hD, psum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      linarith
    exact (hle _ _ hup).1 (hmon _ _).1
  · have hlow : -((a * κ.detShift.natAbs : ℕ) : ℤ) ≤ (D : ℤ) * κ.detShift + (e x : ℤ) := by
      have hD0 : (0 : ℤ) ≤ D := Int.natCast_nonneg D
      have hDa' : (D : ℤ) ≤ a := by exact_mod_cast hDa
      have he0 : (0 : ℤ) ≤ (e x : ℤ) := Int.natCast_nonneg _
      have habs : 0 ≤ κ.detShift + |κ.detShift| := by linarith [neg_abs_le κ.detShift]
      push_cast
      nlinarith [mul_nonneg hD0 habs, mul_nonneg (sub_nonneg.mpr hDa') (abs_nonneg κ.detShift)]
    exact (hle _ _ hlow).2 (hmon _ _).2
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
end
