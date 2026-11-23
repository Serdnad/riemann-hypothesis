module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.UpperBlockRankOneUpdate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
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

open Matrix PositivityTheory.SiegelWeilFormula.Act.C4.Bq

namespace PositivityTheory.SiegelWeilFormula.Act.C6.M

variable {R : Type} [CommRing R] (s : R →+* R) (e : R) {n : ℕ} (i₀ : Fin n)

def U (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) : Prop := Mᵀ * kunf.jw n e * M.map s = kunf.jw n e

variable {s e i₀}

theorem qms_inl (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inl a) d = s (M (Sum.inr a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem qms_inr (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (a : Fin n) (d : Fin n ⊕ Fin n) :
    (kunf.jw n e * M.map s) (Sum.inr a) d = e * s (M (Sum.inl a) d) := by
  simp [kunf.jw, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.smul_apply]

theorem U_apply {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hU : U s e M) (c d : Fin n ⊕ Fin n) :
    ∑ r, M r c * (kunf.jw n e * M.map s) r d = kunf.jw n e c d := by
  have := congrFun (congrFun hU c) d
  rw [Matrix.mul_assoc, Matrix.mul_apply] at this
  simpa [Matrix.transpose_apply] using this

theorem shift_coordinates_column {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    (W : Fin n ⊕ Fin n → R) : ∑ r, M r (Sum.inl i₀) * W r = W (Sum.inl i₀) := by
  have h : ∀ r, M r (Sum.inl i₀) = if r = Sum.inl i₀ then 1 else 0 := fun r => by
    rw [NQ.apply hN (Or.inl rfl), Matrix.one_apply]
  simp_rw [h, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem col_c {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M)
    {c : Fin n ⊕ Fin n} (hcx : c ≠ Sum.inl i₀) (hcy : c ≠ Sum.inr i₀) (W : Fin n ⊕ Fin n → R) :
    ∑ r, M r c * W r = W c + M (Sum.inl i₀) c * W (Sum.inl i₀) := by
  have h : ∀ r, M r c = (if r = c then 1 else 0) + (if r = Sum.inl i₀ then M (Sum.inl i₀) c else 0) := by
    intro r
    by_cases hr : r = Sum.inl i₀
    · subst hr; rw [if_neg (Ne.symm hcx), if_pos rfl, zero_add]
    · rw [NQ.apply hN (Or.inr ⟨hcy, hr⟩), Matrix.one_apply]; simp [hr]
  rw [Finset.sum_congr rfl fun r _ => congrArg (· * W r) (h r)]
  simp_rw [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_split' {A : Type} [AddCommMonoid A] {m : ℕ} (em : Fin m → Fin n) (hem : Function.Injective em)
    (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) (f : Fin n → A) : ∑ a, f a = f i₀ + ∑ j, f (em j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  congr 1
  rw [← Finset.sum_image (fun a _ b _ h => hem h)]
  congr 1
  ext k
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
  exact hrng k

theorem columnBlock (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    M (Sum.inr i₀) (Sum.inr i₀) = 1 ∧ (∀ k, k ≠ i₀ → s (M (Sum.inr k) (Sum.inr i₀)) = -M (Sum.inl i₀) (Sum.inl k)) ∧
      ∀ k, k ≠ i₀ → s (M (Sum.inl k) (Sum.inr i₀)) = -(e * M (Sum.inl i₀) (Sum.inr k)) := by
  set W : Fin n ⊕ Fin n → R := fun r => (kunf.jw n e * M.map s) r (Sum.inr i₀) with hW
  have hyy : s (M (Sum.inr i₀) (Sum.inr i₀)) = 1 := by
    have h1 := U_apply hU (Sum.inl i₀) (Sum.inr i₀)
    rw [shift_coordinates_column hN W] at h1
    simp only [hW, qms_inl] at h1
    simpa [kunf.jw] using h1
  refine ⟨by rw [← hs (M _ _), hyy, map_one], fun k hk => ?_, fun k hk => ?_⟩
  · have h1 := U_apply hU (Sum.inl k) (Sum.inr i₀)
    rw [col_c hN (by simpa using hk) (by simp) W] at h1
    have h2 : s (M (Sum.inr k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inl k) = 0 := by
      simp only [hW, qms_inl, hyy, mul_one] at h1
      simpa [kunf.jw, Matrix.one_apply_ne hk] using h1
    exact eq_neg_of_add_eq_zero_left h2
  · have h1 := U_apply hU (Sum.inr k) (Sum.inr i₀)
    rw [col_c hN (by simp) (by simpa using hk) W] at h1
    have h2 : e * s (M (Sum.inl k) (Sum.inr i₀)) + M (Sum.inl i₀) (Sum.inr k) = 0 := by
      simp only [hW, qms_inl, qms_inr, hyy, mul_one] at h1
      simpa [kunf.jw] using h1
    have h3 := eq_neg_of_add_eq_zero_left h2
    calc s (M (Sum.inl k) (Sum.inr i₀)) = e * (e * s (M (Sum.inl k) (Sum.inr i₀))) := by rw [← mul_assoc, he, one_mul]
      _ = -(e * M (Sum.inl i₀) (Sum.inr k)) := by rw [h3, mul_neg]

theorem nq_unique (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e)
    {M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R} (hM : U s e M) (hN : U s e N)
    (hMq : NQ (Sum.inl i₀) (Sum.inr i₀) M) (hNq : NQ (Sum.inl i₀) (Sum.inr i₀) N)
    (hrow : ∀ c, M (Sum.inl i₀) c = N (Sum.inl i₀) c) : M = N := by
  obtain ⟨hM1, hM2, hM3⟩ := columnBlock hs he hse hM hMq
  obtain ⟨hN1, hN2, hN3⟩ := columnBlock hs he hse hN hNq
  have hinj : Function.Injective s := fun a b h => by rw [← hs a, h, hs b]
  ext r c
  by_cases hrx : r = Sum.inl i₀
  · subst hrx; exact hrow c
  by_cases hcy : c = Sum.inr i₀
  · subst hcy
    rcases r with k | k
    · have hk : k ≠ i₀ := fun h => hrx (by rw [h])
      exact hinj (by rw [hM3 k hk, hN3 k hk, hrow])
    · by_cases hk : k = i₀
      · subst hk; rw [hM1, hN1]
      · exact hinj (by rw [hM2 k hk, hN2 k hk, hrow])
  · rw [NQ.apply hMq (Or.inr ⟨hcy, hrx⟩), NQ.apply hNq (Or.inr ⟨hcy, hrx⟩)]

theorem even_im_hermitian_sub (hs : ∀ a, s (s a) = a) (he : e * e = 1) (hse : s e = e) {m : ℕ} (em : Fin m → Fin n)
    (hem : Function.Injective em) (hrng : ∀ k, k ≠ i₀ ↔ k ∈ Set.range em) {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R}
    (hU : U s e M) (hN : NQ (Sum.inl i₀) (Sum.inr i₀) M) :
    s (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))) =
      -(e * (M (Sum.inl i₀) (Sum.inr i₀) + ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j))))) := by
  obtain ⟨h1, h2, h3⟩ := columnBlock hs he hse hU hN
  have hem0 : ∀ j, em j ≠ i₀ := fun j => (hrng (em j)).2 ⟨j, rfl⟩
  have hl : ∀ j, M (Sum.inl (em j)) (Sum.inr i₀) = -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) := fun j => by
    rw [← hs (M (Sum.inl (em j)) (Sum.inr i₀)), h3 _ (hem0 j), map_neg, map_mul, hse]
  have hr : ∀ j, M (Sum.inr (em j)) (Sum.inr i₀) = -s (M (Sum.inl i₀) (Sum.inl (em j))) := fun j => by
    rw [← hs (M (Sum.inr (em j)) (Sum.inr i₀)), h2 _ (hem0 j), map_neg]
  have hyy : M (Sum.inr i₀) (Sum.inr i₀) = 1 := h1
  have h0 := U_apply hU (Sum.inr i₀) (Sum.inr i₀)
  rw [Fintype.sum_sum_type] at h0
  simp only [qms_inl, qms_inr] at h0
  rw [sum_split' em hem hrng (fun a => M (Sum.inl a) (Sum.inr i₀) * s (M (Sum.inr a) (Sum.inr i₀))),
    sum_split' em hem hrng (fun a => M (Sum.inr a) (Sum.inr i₀) * (e * s (M (Sum.inl a) (Sum.inr i₀))))] at h0
  simp only [hl, hr, hyy, map_one, map_neg, map_mul, hs, hse, kunf.jw, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] at h0
  set α := M (Sum.inl i₀) (Sum.inr i₀)
  set S1 := ∑ j, s (M (Sum.inl i₀) (Sum.inr (em j))) * M (Sum.inl i₀) (Sum.inl (em j))
  set S2 := ∑ j, M (Sum.inl i₀) (Sum.inr (em j)) * s (M (Sum.inl i₀) (Sum.inl (em j)))
  have hA : ∑ j, -(e * s (M (Sum.inl i₀) (Sum.inr (em j)))) * -M (Sum.inl i₀) (Sum.inl (em j)) = e * S1 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hB : ∑ j, -s (M (Sum.inl i₀) (Sum.inl (em j))) * (e * -(e * M (Sum.inl i₀) (Sum.inr (em j)))) = (e * e) * S2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hA, hB, he, one_mul] at h0
  have hS : s S2 = S1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S2, S1, map_sum, map_mul, hs]
  rw [map_add (f := _), hS]
  linear_combination e * h0 - (s α + S1) * he

end PositivityTheory.SiegelWeilFormula.Act.C6.M

end
end

section

noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n k : ℕ} (i₀ : Fin n) (em : Fin k → Fin n)

def cB (u v : Fin k → R) (z : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (1 + ∑ j, Matrix.single i₀ (em j) (u j)) (Matrix.single i₀ i₀ z) 0 (1 - ∑ j, Matrix.single (em j) i₀ (v j))

variable {i₀ em}

theorem cB_mul (hem : ∀ j, em j ≠ i₀) (u v : Fin k → R) (z : R) : cB i₀ em u v z * cB i₀ em (-u) (-v) (-z) = 1 := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, Matrix.fromBlocks_multiply, Pi.neg_apply, ← Matrix.single_neg,
    Finset.sum_neg_distrib]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, one_mul, mul_one, mul_zero, zero_mul,
      hPP, hQQ, hPZ, hZQ, neg_zero, add_zero, zero_add, sub_zero, neg_neg] <;>
    abel

theorem cB_unitary (hem : ∀ j, em j ≠ i₀) (f : R →+* R) (hf : ∀ a, f (f a) = a) (e : R) (he : e * e = 1)
    (u : Fin k → R) (z : R) (hz : f z = -(e * z)) :
    (cB i₀ em u (fun j => f (u j)) z)ᵀ * kunf.jw n e * (cB i₀ em u (fun j => f (u j)) z).map f = kunf.jw n e := by
  have hPP : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single i₀ (em j) (w j)) * (∑ j, Matrix.single i₀ (em j) (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hQQ : ∀ w w' : Fin k → R,
      (∑ j, Matrix.single (em j) i₀ (w j)) * (∑ j, Matrix.single (em j) i₀ (w' j)) = 0 := by
    intro w w'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun l _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem l).symm _
  have hPZ : ∀ (w : Fin k → R) (c : R),
      (∑ j, Matrix.single i₀ (em j) (w j)) * Matrix.single i₀ i₀ c = 0 := by
    intro w c
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j) _
  have hZQ : ∀ (w : Fin k → R) (c : R),
      Matrix.single i₀ i₀ c * (∑ j, Matrix.single (em j) i₀ (w j)) = 0 := by
    intro w c
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun j _ => Matrix.single_mul_single_of_ne _ _ _ _ (hem j).symm _
  have hmap : ∀ M : Matrix (Fin n) (Fin n) R, M.map f = f.mapMatrix M := fun M =>
    (RingHom.mapMatrix_apply f M).symm

  simp only [PositivityTheory.SiegelWeilFormula.Act.CL.cB, PositivityTheory.SiegelWeilFormula.kunf.jw, Matrix.fromBlocks_transpose,
  Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_add, Matrix.transpose_sub,
  Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_sum, Matrix.transpose_single, hmap,
  map_add, map_sub, map_one, map_zero, map_sum]
  simp only [RingHom.mapMatrix_apply, Matrix.map_single, hf, hz]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [mul_zero, zero_mul, add_zero]
  · simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_sub, add_mul, one_mul, hQQ, sub_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one]
    congr 1
    simp only [mul_add, sub_mul, one_mul, mul_one, hPP, add_zero]
    abel
  · simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      mul_sub, sub_mul, one_mul, hPZ, hZQ, sub_zero, Matrix.smul_single, smul_eq_mul, smul_zero]
    rw [← Matrix.single_add, show e * -(e * z) + z = 0 by linear_combination (-z) * he, Matrix.single_zero]

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.CL

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem ptEx' (d : SD σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  have hone : incM F (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.mul_inv, hone]
  have hQP : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
    rw [← PositivityTheory.SiegelWeilFormula.kunf.incM_mul', Units.inv_mul, hone]
  have hM'M : ∀ c, M' c * M c = 1 := fun c => by
    first
    | exact mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_comm.mp (h c)
    | exact Matrix.mul_eq_one_symm (h c)
  let N : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M c * incM F (d.b⁻¹).1
  let N' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
    fun c => incM F d.b.1 * M' c * incM F (d.b⁻¹).1
  have hNN' : ∀ c, N c * N' c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M c) (M' c), h c, Matrix.one_mul, hPQ]
  have hN'N : ∀ c, N' c * N c = 1 := by
    intro c
    simp only [N, N', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), hQP, Matrix.one_mul,
      ← Matrix.mul_assoc (M' c) (M c), hM'M c, Matrix.one_mul, hPQ]
  let u : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨N c, N' c, hNN' c, hN'N c⟩
  have mem : ∀ c, u c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε (M c) (M' c) (h c) (hu c)
    have hx' : x.1.1 = N c := by
      show x.1.1 = incM F d.b.1 * M c * incM F (d.b⁻¹).1
      rw [← hx]
      show x.1.1 = incM F d.b.1 * (incM F (d.b⁻¹).1 * x.1.1 * incM F d.b.1) * incM F (d.b⁻¹).1
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
    have e : u c = x.1 := Units.ext hx'.symm
    rw [e]
    exact x.2
  refine ⟨fun c => ⟨u c, mem c⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · intro c
    show incM F (d.b⁻¹).1 * N c * incM F d.b.1 = M c
    simp only [N, Matrix.mul_assoc]
    rw [hQP, Matrix.mul_one, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

end PositivityTheory.SiegelWeilFormula.Act.CL

end
end
