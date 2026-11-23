module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle499
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle500
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Sep

variable {D : D7} {r : ℕ}

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR]
  rw [h]
  exact (hθ τ).1 x

theorem pairF_eq {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (a β : HermE D r) :
    pairF θ α a β =
      -∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (β.1 * a.1))).re := by
  unfold pairF lam
  simp only [← map_mul, theta_incA hθ]

def hermQ (D : D7) (r : ℕ) : Submodule ℚ (Matrix (Fin r) (Fin r) D.host.E) where
  carrier := {b | (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    simp only [Matrix.add_apply, map_add (f := _), h1, h2]
  zero_mem' := by
    ext i j
    simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    simp only [Matrix.smul_apply, map_rat_smul, h1]

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ, -⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 w
  exact ⟨τ⟩

theorem mem_hermQ {b : Matrix (Fin r) (Fin r) D.host.E} :
    b ∈ hermQ D r ↔ ∀ i j, D.sp.cm.sig (b j i) = b i j := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    exact Matrix.ext fun i j => h i j

def formH (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) : hermQ D r →+ ℝ :=
  AddMonoidHom.mk'
    (fun a => ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re)
    (by
      intro a b
      simp only [Submodule.coe_add, mul_add, Matrix.trace_add, map_add (f := _), Complex.add_re,
        Finset.sum_add_distrib])

theorem formH_apply (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α δ a =
      ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re := rfl

theorem formH_eq_zero {d : ℕ} (b : Module.Basis (Fin d) ℚ (hermQ D r)) {α : D.host.F}
    {δ : Matrix (Fin r) (Fin r) D.host.E} (h : ∀ k, formH α δ (b k) = 0) (a : hermQ D r) :
    formH α δ a = 0 := by
  have e : (formH α δ).toRatLinearMap = 0 := b.ext (fun k => by simpa using h k)
  simpa using LinearMap.congr_fun e a

theorem formH_sub_left (α : D.host.F) (b b' : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α (b - b') a = formH α b a - formH α b' a := by
  simp only [formH_apply, sub_mul, Matrix.trace_sub, mul_sub, map_sub, Complex.sub_re,
    Finset.sum_sub_distrib]

theorem pairF_eq_formH {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β : HermE D r)
    (a : hermQ D r) : pairF θ α ⟨a.1, a.2⟩ β = -formH α β.1 a :=
  pairF_eq hθ α ⟨a.1, a.2⟩ β

theorem formH_sub {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β β' : HermE D r)
    (a : hermQ D r) :
    formH α (β.1 - β'.1) a = pairF θ α ⟨a.1, a.2⟩ β' - pairF θ α ⟨a.1, a.2⟩ β := by
  have e := pairF_eq_formH hθ α β a
  have e' := pairF_eq_formH hθ α β' a
  have e'' := formH_sub_left α β.1 β'.1 a
  linarith

theorem trace_sq_ne_zero {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) (h0 : δ ≠ 0) :
    Matrix.trace (δ * δ) ≠ 0 := by
  intro hn
  obtain ⟨τ⟩ := tau_nonempty D
  have hm := mem_hermQ.1 hδ
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hc : ∀ i j, tauE D τ (δ j i) = starRingEnd ℂ (tauE D τ (δ i j)) := by
    intro i j
    rw [← hm j i]
    exact hcm.2.2.2 _ _
  have hs : ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) = 0 := by
    have e : tauE D τ (Matrix.trace (δ * δ)) =
        ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) := by
      push_cast

      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hc i j, Complex.mul_conj]
    rw [← e, hn, map_zero]
  have hs' : (∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j))) = 0 := by exact_mod_cast hs
  apply h0
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 hs' i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg _)).1 h1 j (Finset.mem_univ j)
  have h3 : tauE D τ (δ i j) = 0 := Complex.normSq_eq_zero.1 h2
  simpa using h3

theorem sig_trace_sq {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) :
    D.sp.cm.sig (Matrix.trace (δ * δ)) = Matrix.trace (δ * δ) := by
  have hm := mem_hermQ.1 hδ

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hm]
  rw [Finset.sum_comm]

theorem inv_smul_mem {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) {x : D.host.E}
    (hx : D.sp.cm.sig x = x) : x⁻¹ • δ ∈ hermQ D r := by
  have hm := mem_hermQ.1 hδ
  refine mem_hermQ.2 fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hx, hm]

theorem exists_separating : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 →
    ∃ (d : ℕ) (a : Fin d → HermE D r),
      Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  intro D r θ hθ α hα
  let b := Module.finBasis ℚ (hermQ D r)
  refine ⟨_, fun k => ⟨(b k).1, (b k).2⟩, ?_⟩
  intro β β' h
  by_contra hne
  have hδ : β.1 - β'.1 ∈ hermQ D r :=
    sub_mem (show β.1 ∈ hermQ D r from β.2) (show β'.1 ∈ hermQ D r from β'.2)
  have hδ0 : β.1 - β'.1 ≠ 0 := sub_ne_zero.2 fun e => hne (Subtype.ext e)
  have hz : ∀ a, formH α (β.1 - β'.1) a = 0 := by
    refine formH_eq_zero b fun k => ?_
    rw [formH_sub hθ]
    have := congrFun h k
    exact sub_eq_zero.2 this.symm
  set δ := β.1 - β'.1 with hδdef
  have hn := trace_sq_ne_zero hδ hδ0
  have hαE : algebraMap D.host.F D.host.E α ≠ 0 := by
    simpa using hα
  set x := algebraMap D.host.F D.host.E α * Matrix.trace (δ * δ) with hx
  have hx0 : x ≠ 0 := mul_ne_zero hαE hn
  have hxs : D.sp.cm.sig x = x := by
    rw [hx, map_mul, sig_trace_sq hδ, AlgHom.commutes]
  have hv := hz ⟨x⁻¹ • δ, inv_smul_mem hδ hxs⟩
  rw [formH_apply] at hv
  have h1 : algebraMap D.host.F D.host.E α * Matrix.trace (δ * (x⁻¹ • δ)) = 1 := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_comm _ x⁻¹, mul_assoc,
      ← hx, inv_mul_cancel₀ hx0]
  simp only [h1, map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hv
  haveI := tau_nonempty D
  have : (Fintype.card D.what₂.Tau : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact this hv

end GlobalTheory.CompanionTheory.WSum.Sep
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.ParStab

section Linear

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def firstCols (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] : Matrix (ι ⊕ ι) ι R := Matrix.fromRows 1 0

theorem mul_firstCols (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : g * firstCols R ι = g.toCols₁ := by
  ext r j
  simp [firstCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem firstCols_mul_apply_inl (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inl i) j = m i j := by
  simp [firstCols, Matrix.mul_apply, Matrix.one_apply]

theorem firstCols_mul_apply_inr (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inr i) j = 0 := by
  simp [firstCols, Matrix.mul_apply]

theorem firstCols_cancel {m m' : Matrix ι ι R} (h : firstCols R ι * m = firstCols R ι * m') : m = m' := by
  ext i j
  rw [← firstCols_mul_apply_inl m, h, firstCols_mul_apply_inl]

theorem low_zero_of_mul {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} {m : Matrix ι ι R} (h : g * firstCols R ι = firstCols R ι * m)
    (i j : ι) : g (Sum.inr i) (Sum.inl j) = 0 := by
  have := congrFun (congrFun h (Sum.inr i)) j
  rwa [mul_firstCols, firstCols_mul_apply_inr] at this

theorem mul_eq_of_low_zero {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : ∀ i j, g (Sum.inr i) (Sum.inl j) = 0) :
    g * firstCols R ι = firstCols R ι * g.toBlocks₁₁ := by
  ext r j
  rcases r with i | i
  · rw [firstCols_mul_apply_inl, mul_firstCols]; rfl
  · rw [firstCols_mul_apply_inr, mul_firstCols]; exact h i j

theorem mem_stab_iff (g : GL (ι ⊕ ι) R) : g ∈ stab R (Sum.inl '' (Set.univ : Set ι)) ↔
    ∀ i j, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro h i j
    exact h (Sum.inr i) (by simp) (Sum.inl j) (by simp)
  · intro h r hr c hc
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, Set.mem_univ _, rfl⟩ hr
    · exact h i j

theorem exists_mul_eq_iff_mem_stab (B x : GL (ι ⊕ ι) R) (D : Matrix (ι ⊕ ι) ι R) (T : GL ι R)
    (hB : (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι = D * (T : Matrix ι ι R)) :
    (∃ t : GL ι R, (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * (t : Matrix ι ι R)) ↔
      B⁻¹ * x * B ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := by
  have hBi : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTi : (T : Matrix ι ι R) * ((T⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD : D = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
    rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have hC : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R) = firstCols R ι := by
    rw [Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hinv : (B⁻¹ * x * B)⁻¹ = B⁻¹ * x⁻¹ * B := by group
  have key : ∀ (g : GL (ι ⊕ ι) R) (s : Matrix ι ι R), (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * s →
      ((B⁻¹ * g * B : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι =
        firstCols R ι * (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
    intro g s hg
    calc _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * (T : Matrix ι ι R) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [hB]
      _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (s * (T : Matrix ι ι R)) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = (((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R)) *
            (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (T : Matrix ι ι R) (((T⁻¹ : GL ι R) : Matrix ι ι R)), hTi, Matrix.one_mul]
      _ = _ := by rw [hC]
  constructor
  · rintro ⟨t, ht⟩
    have hx' : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
      have h1 : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (D * ((t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R))) := by
            rw [h2, Matrix.mul_one]
        _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
            rw [ht]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [mem_stab_iff]
    intro i j
    refine ⟨low_zero_of_mul (key x _ ht) i j, ?_⟩
    rw [hinv]
    exact low_zero_of_mul (key x⁻¹ _ hx') i j
  · intro hy
    rw [mem_stab_iff] at hy
    set y : GL (ι ⊕ ι) R := B⁻¹ * x * B with hydef
    have e1 := mul_eq_of_low_zero fun i j => (hy i j).1
    have e2 := mul_eq_of_low_zero fun i j => (hy i j).2
    set m := (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm
    set m' := ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm'
    have hyy : (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hyy' : ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmm : m * m' = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hyy, Matrix.one_mul, Matrix.mul_one]
    have hmm' : m' * m = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e2, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, hyy', Matrix.one_mul, Matrix.mul_one]
    let u : GL ι R := ⟨m, m', hmm, hmm'⟩
    refine ⟨T * u * T⁻¹, ?_⟩
    have hx : (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
        (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hydef]
      group
    calc _ = (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          conv_lhs => rw [hD]
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι) * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          rw [hx]; simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by
          rw [e1]; simp only [Matrix.mul_assoc]
      _ = D * (T : Matrix ι ι R) * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by rw [hB]
      _ = _ := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rfl

end Linear

theorem exists_isPar_iff_mem_uQ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht x
  have hdiag : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) =
      diagCols (Fin n) := by
    ext r j
    rcases r with i | i <;> by_cases h : i = j <;> simp [diagCols, Matrix.one_apply, h]
  have hB : ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * firstCols (AE F E) (Fin n) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) t₀ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mul_firstCols, ← hdiag]
    have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E) := ht
    have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) ht'
    simp only [Matrix.map_mul] at this
    exact this
  have h := exists_mul_eq_iff_mem_stab (bA (F := F) b) x.1 (diagCols (Fin n)) _ hB
  rw [PositivityTheory.RgEis.Ad.uQ, Subgroup.mem_subgroupOf, frameEquiv_val]
  exact h

end GlobalTheory.CompanionTheory.SiegelFrame.ParStab
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.StdCompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem conj_unit_iff {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = 1 ↔ U * Uᴴ = 1 := by
  have e : U.map (starRingEnd ℂ) * (U.map (starRingEnd ℂ))ᴴ = (U * Uᴴ).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
  constructor
  · intro h
    rw [e] at h
    have h2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = (1 : Matrix ι ι ℂ).map (starRingEnd ℂ) := by rw [h]
    have e2 : ((U * Uᴴ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = U * Uᴴ := by
      ext i j
      simp only [Matrix.map_apply, Complex.conj_conj]
    rw [e2, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  · intro h
    rw [e, h]
    exact Matrix.map_one _ (map_zero _) (map_one _)

theorem inFrame_eq (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E)
    (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (x : G2 σ Y) :
    inFrame b x = (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
  have hinv : (bA (F := F) b)⁻¹ = bA (F := F) b⁻¹ :=
    (map_inv (Matrix.GeneralLinearGroup.map (n := Fin n ⊕ Fin n) (inclR (F := F) (E := E) (AF F))) b).symm
  rw [frameEquiv_val, hinv]
  rfl

theorem mem_O_iff (hD : Dict) (χ : Chr F E) (y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    y ∈ (adCM σ χ).O ↔ finOne F • y ∈ intHat F E :=
  (hD F E).2.2.2.1 y

theorem unit_iff (hI : DictInf) (hcm : IsCMExt F E σ) (χ : Chr F E) (B : Base F E)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    (∀ w, M.map (piInf (B.emb w)) * (M.map (piInf (B.emb w)))ᴴ = 1) ↔
      ∀ w, M.map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  have key : ∀ (τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* ℂ) (w' : InfinitePlace E),
      ((∀ z, τ z = (adStd E).φ w' (eqv F E z)) ∨ ∀ z, τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z))) →
      (M.map τ * (M.map τ)ᴴ = 1 ↔ M.map ((adCM σ χ).φ w') ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ) := by
    intro τ w' h
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    rcases h with h | h
    · have e : M.map τ = M.map ((adCM σ χ).φ w') := by
        ext i j
        exact h _
      rw [e]
    · have e : M.map τ = (M.map ((adCM σ χ).φ w')).map (starRingEnd ℂ) := by
        ext i j
        exact h _
      rw [e]
      exact conj_unit_iff _
  obtain ⟨h1, h2⟩ := (hI F E σ hcm).2 B.emb
  constructor
  · intro h w'
    obtain ⟨w, hw⟩ := h2 w'
    exact (key _ w' hw).1 (h w)
  · intro h w
    obtain ⟨w', hw⟩ := h1 w
    exact (key _ w' hw).2 (h w')

theorem mem_isStdK_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  intro F E _ _ _ _ _ σ n Y hD hI hcm χ ε b hb B K hK x
  have hinv : inFrame b x⁻¹ = ((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
    rw [inFrame_eq χ ε b hb x⁻¹, map_inv]
    rfl
  have hx := inFrame_eq χ ε b hb x
  rw [hK x]
  show _ ↔ (frameEquiv χ ε b hb x).1 ∈ (adCM σ χ).kGL (Fin n ⊕ Fin n)
  show _ ↔ (∀ r c, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) r c ∈ (adCM σ χ).O ∧
      (((((frameEquiv χ ε b hb x).1)⁻¹ : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) r c ∈ (adCM σ χ).O) ∧
      ∀ w, (((frameEquiv χ ε b hb x).1 : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map ((adCM σ χ).φ w) ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ
  rw [← hinv, ← hx, ← unit_iff hI hcm χ B, and_comm]
  refine and_congr ?_ Iff.rfl
  simp only [mem_O_iff (σ := σ) hD χ]
  constructor
  · intro h r c
    exact ⟨h x (by simp) r c, h x⁻¹ (by simp) r c⟩
  · intro h k' hk' r c
    rcases hk' with rfl | hk'
    · exact (h r c).1
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      exact (h r c).2

end GlobalTheory.CompanionTheory.SiegelFrame.StdCompact
end
end
