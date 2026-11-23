module

public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Module.PID
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

section

open Polynomial

noncomputable def UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField :
    Prop :=
    ∀ (A B : Type) [inst : CommRing A] [inst_1 : IsDomain A] [inst_2 : CommRing B] [inst_3 : Algebra A B]
      [Module.Finite A B],
      ∃ (L : Type) (x : Field L) (x_1 : Algebra A L) (x_2 : Algebra (FractionRing A) L) (_ :
        IsScalarTower A (FractionRing A) L),
        FiniteDimensional (FractionRing A) L ∧
          Normal (FractionRing A) L ∧
            Finite (B →ₐ[A] ↥(integralClosure A L)) ∧
              ∀ (Ω : Type) [inst_5 : Field Ω] (φ : ↥(integralClosure A L) →+* Ω) (z : B →+* Ω),
                Function.Injective (⇑(φ.comp (Algebra.algebraMap A ↥(integralClosure A L))) : A → Ω) →
                  z.comp (Algebra.algebraMap A B) = φ.comp (Algebra.algebraMap A ↥(integralClosure A L)) →
                    ∃! σ : B →ₐ[A] ↥(integralClosure A L), φ.comp (↑σ : B →+* ↥(integralClosure A L)) = z

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (s : Finset B) :
    ∃ p : A[X], p.Monic ∧ ∀ b ∈ s, aeval b p = 0 := by
  have h : ∀ b : B, ∃ q : A[X], q.Monic ∧ aeval b q = 0 := fun b =>
    (Algebra.IsIntegral.isIntegral (R := A) b)
  choose q hq hq0 using h
  refine ⟨∏ b ∈ s, q b, monic_prod_of_monic _ _ fun b _ => hq b, fun b hb => ?_⟩
  rw [map_prod]
  exact Finset.prod_eq_zero hb (hq0 b)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom {A B C : Type} [CommRing A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] (s : Finset B)
    (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) : Finite (B →ₐ[A] C) := by
  let f : (B →ₐ[A] C) → (s → p.rootSet C) := fun σ b =>
    ⟨σ b, by
      rw [hp.mem_rootSet, aeval_algHom_apply, h0 b b.2, map_zero]⟩
  refine Finite.of_injective f fun σ τ h => ?_
  apply AlgHom.toLinearMap_injective
  refine LinearMap.ext_on hs fun b hb => ?_
  exact congrArg Subtype.val (congrFun h ⟨b, hb⟩)

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.factor {A B C Ω : Type} [CommRing A] [Nontrivial A] [CommRing B]
    [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra.IsIntegral A C] [Field Ω]
    (s : Finset B) (hs : Submodule.span A (s : Set B) = ⊤) (p : A[X]) (hp : p.Monic)
    (h0 : ∀ b ∈ s, aeval b p = 0) (hsp : (p.map (algebraMap A C)).Splits)
    (φ : C →+* Ω) (z : B →+* Ω) (hinj : Function.Injective (φ.comp (algebraMap A C)))
    (hz : z.comp (algebraMap A B) = φ.comp (algebraMap A C)) :
    ∃! σ : B →ₐ[A] C, φ.comp (σ : B →+* C) = z := by
  have hφ : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    rw [Ideal.under_def, RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hzA : ∀ a : A, z (algebraMap A B a) = φ (algebraMap A C a) := fun a =>
    DFunLike.congr_fun hz a
  have hgen : ∀ b ∈ s, z b ∈ φ.range := by
    intro b hb
    have h1 : eval (z b) ((p.map (algebraMap A C)).map φ) = 0 := by
      rw [Polynomial.map_map, ← hz, eval_map, ← hom_eval₂, ← aeval_def, h0 b hb, map_zero]
    rw [hsp.eq_prod_roots_of_monic (hp.map _), Polynomial.map_multiset_prod,
      eval_multiset_prod, Multiset.prod_eq_zero_iff] at h1
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub,
      map_X, map_C, eval_sub, eval_X, eval_C] at h1
    obtain ⟨c, -, hc⟩ := h1
    exact ⟨c, (sub_eq_zero.1 hc).symm⟩
  have hall : ∀ b : B, z b ∈ φ.range := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, hzA]
      exact mul_mem ⟨_, rfl⟩ hx
  choose g hg using hall
  let σ : B →ₐ[A] C :=
    { toFun := g
      map_one' := hφ (by rw [hg, map_one, map_one])
      map_mul' := fun x y => hφ (by rw [map_mul φ, hg, hg, hg, map_mul])
      map_zero' := hφ (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => hφ (by rw [map_add φ, hg, hg, hg, map_add (f := _)])
      commutes' := fun a => hφ (by rw [hg, hzA]) }
  refine ⟨σ, RingHom.ext fun b => hg b, fun τ hτ => AlgHom.ext fun b => hφ ?_⟩
  exact (DFunLike.congr_fun hτ b).trans (hg b).symm

private theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure {A L : Type} [CommRing A] [Field L]
    [Algebra A L] (p : A[X]) (hp : p.Monic) (hsp : (p.map (algebraMap A L)).Splits) :
    (p.map (algebraMap A (integralClosure A L))).Splits := by
  have hm : (p.map (algebraMap A (integralClosure A L))).map
      (algebraMap (integralClosure A L) L) = p.map (algebraMap A L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  refine Splits.of_splits_map_of_injective (i := algebraMap (integralClosure A L) L)
    Subtype.val_injective (hm ▸ hsp) fun a ha => ?_
  rw [hm] at ha
  have h1 := isRoot_of_mem_roots ha
  rw [IsRoot.def, eval_map] at h1
  exact ⟨⟨a, p, hp, h1⟩, rfl⟩

theorem UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of :
    UpperTheory.Reformulated.B.SplittingFieldConstruction.SplitField := by
  intro A B _ _ _ _ _
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨p, hp, h0⟩ := UpperTheory.Reformulated.B.SplittingFieldConstruction.exists_monic (A := A) s
  let q : (FractionRing A)[X] := p.map (algebraMap A (FractionRing A))
  let L : Type := q.SplittingField
  letI iK : Algebra (FractionRing A) L := inferInstance
  letI iA : Algebra A L :=
    ((algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))).toAlgebra
  haveI iT : @IsScalarTower A (FractionRing A) L Algebra.toSMul iK.toSMul iA.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hsp : (p.map (algebraMap A L)).Splits := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L, ← Polynomial.map_map]
    exact SplittingField.splits q
  refine ⟨L, inferInstance, iA, iK, iT, inferInstance, inferInstance,
    UpperTheory.Reformulated.B.SplittingFieldConstruction.finite_algHom s hs p hp h0, ?_⟩
  intro Ω _ φ z hinj hz
  exact UpperTheory.Reformulated.B.SplittingFieldConstruction.factor s hs p hp h0
    (UpperTheory.Reformulated.B.SplittingFieldConstruction.splits_closure p hp hsp) φ z hinj hz
end

section

noncomputable def UpperTheory.Reformulated.B.G8.kry :
    {R : Type} → [CommRing R] → {n : ℕ} → Matrix (Fin n) (Fin n) R → (Fin n → R) → Matrix (Fin n) (Fin n) R :=
    fun {R : Type} [CommRing R] {n : ℕ} (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦ (g ^ (↑j : ℕ)).mulVec v i

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) (p : K[X])
    (hp : p.degree < n) (h0 : aeval g p = 0) : p = 0 := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using hp
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let L := AlgebraicClosure K
  let f : K →+* L := algebraMap K L
  let G : Matrix (Fin n) (Fin n) L := g.map f
  have hG : G.charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hg.map
  have hG0 : aeval G (p.map f) = 0 := by
    have h1 := congrArg (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId K L)) h0
    rw [map_zero, ← aeval_algHom_apply] at h1
    rw [aeval_map_algebraMap]
    exact h1
  have hcard : G.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hG), ← (IsAlgClosed.splits G.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hz : p.map f = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero G.charpoly.roots.toFinset ?_ ?_
    · rw [hcard, degree_map]
      exact hp
    · intro x hx
      have hx' : x ∈ spectrum L G :=
        Matrix.mem_spectrum_of_isRoot_charpoly (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx))
      have h2 := spectrum.subset_polynomial_aeval G (p.map f) ⟨x, hx', rfl⟩
      rw [hG0, spectrum.zero_eq] at h2
      exact h2
  exact (Polynomial.map_eq_zero_iff f.injective).mp hz

open Polynomial in
private theorem UpperTheory.Reformulated.B.G8.exists_kry_field {K : Type} [Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K) (hg : g.charpoly.Separable) :
    ∃ v : Fin n → K, (UpperTheory.Reformulated.B.G8.kry g v).det ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator K[X]
    (Module.AEval K (Fin n → K) g)
  obtain ⟨v, rfl⟩ := (Module.AEval.of K (Fin n → K) g).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : K[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hdeg : p.degree < n := degree_sum_fin_lt c
  have hv : aeval g p • v = 0 := by
    rw [← hc0]
    ext i

    simp only [p, map_sum, map_mul, aeval_C, map_pow, aeval_X, Finset.sum_smul, Finset.sum_apply,
    ← Algebra.smul_def, smul_assoc, Pi.smul_apply, smul_eq_mul, Matrix.smul_eq_mulVec]
    simp only [UpperTheory.Reformulated.B.G8.kry, Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hker : p ∈ Module.annihilator K[X] (Module.AEval K (Fin n → K) g) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← Module.AEval.of_aeval_smul,
      hv, map_zero]
  have hp0 : aeval g p = 0 := by
    refine Matrix.ext_iff_mulVec.mpr fun w => ?_
    have h1 := Module.mem_annihilator.mp hker (Module.AEval.of K (Fin n → K) g w)
    rw [← Module.AEval.of_aeval_smul, map_eq_zero_iff _ (LinearEquiv.injective _)] at h1
    rw [Matrix.zero_mulVec]
    exact h1
  have hp : p = 0 := UpperTheory.Reformulated.B.G8.eq_zero_of_aeval_eq_zero g hg p hdeg hp0
  apply hc
  ext j
  have h1 := congrArg (fun q => q.coeff j) hp
  simpa [p, finsetSum_coeff, coeff_X_pow, Fin.val_inj] using h1

private theorem UpperTheory.Reformulated.B.G8.kry_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (g : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    f (UpperTheory.Reformulated.B.G8.kry g v).det = (UpperTheory.Reformulated.B.G8.kry (g.map f) (f ∘ v)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [UpperTheory.Reformulated.B.G8.kry, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec, Matrix.map_pow]

theorem UpperTheory.Reformulated.B.G8.exists_kry :
    ∀ {R : Type} [inst : CommRing R] [Finite (MaximalSpectrum R)] {n : ℕ} (g : Matrix (Fin n) (Fin n) R),
      g.charpoly.Separable → ∃ (v : Fin n → R), IsUnit (UpperTheory.Reformulated.B.G8.kry g v).det := by
  intro R _ _ n g hg
  have h1 : ∀ m : MaximalSpectrum R, ∃ w : Fin n → R ⧸ m.asIdeal,
      (UpperTheory.Reformulated.B.G8.kry (g.map (Ideal.Quotient.mk m.asIdeal)) w).det ≠ 0 := by
    intro m
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    refine UpperTheory.Reformulated.B.G8.exists_kry_field _ ?_
    rw [Matrix.charpoly_map]
    exact hg.map
  choose w hw using h1
  have hco : Pairwise (Function.onFun IsCoprime fun m : MaximalSpectrum R => m.asIdeal) := by
    intro a b hab
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (a.isMaximal.coprime_of_ne b.isMaximal fun h => hab (MaximalSpectrum.ext h))
  choose v hv using fun i : Fin n => Ideal.pi_quotient_surjective hco fun m => w m i
  refine ⟨v, ?_⟩
  by_contra hu
  obtain ⟨M, hM, hmem⟩ := exists_max_ideal_of_mem_nonunits hu
  apply hw ⟨M, hM⟩
  have h2 : w ⟨M, hM⟩ = Ideal.Quotient.mk M ∘ v := funext fun i => (hv i ⟨M, hM⟩).symm
  rw [h2, ← UpperTheory.Reformulated.B.G8.kry_map]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qf25.modFun :
    {O M ι : Type} → [inst : CommRing O] → [inst_1 : AddCommGroup M] → [_root_.Module O M] → _root_.Module O (ι → M) :=
    fun {O M ι : Type} [CommRing O] [AddCommGroup M] [_root_.Module O M] ↦ Pi.Function.module ι O M
attribute [local instance] UpperTheory.Reformulated.B.Qf25.modFun

theorem UpperTheory.Reformulated.B.Qf25.trace_zero :
    ∀ {k : Type} [inst : Field k] (S T : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k),
      T.det ≠ (0 : k) →
        S.charpoly.Separable →
          ∀ (v : Fin (2 : ℕ) → k),
            v ≠ (0 : Fin (2 : ℕ) → k) →
              T.mulVec v ∉ k ∙ v →
                ∀ (a b c : k),
                  S.mulVec v = a • v →
                    S.mulVec (T.mulVec v) = b • T.mulVec v →
                      S.mulVec (T.mulVec (T.mulVec v)) = c • T.mulVec (T.mulVec v) → T.trace = (0 : k) := by
  intro k _ S T hdet hsep v hv hw a b c ha hb hc
  have hCH : T.mulVec (T.mulVec v) = T.trace • T.mulVec v - T.det • v := by
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.trace_fin_two,
        Matrix.det_fin_two] <;> ring
  generalize T.mulVec v = w at hw hb hc hCH
  have hD : v 0 * w 1 - v 1 * w 0 ≠ 0 := by
    intro h
    apply hw
    rw [Submodule.mem_span_singleton]
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i
        · exact h0
        · exact h1
      have hw0 : w 0 = 0 := by
        have : v 1 * w 0 = 0 := by linear_combination -h + w 1 * h0
        exact (mul_eq_zero.1 this).resolve_left h1
      refine ⟨w 1 / v 1, ?_⟩
      ext i
      fin_cases i
      · simp [h0, hw0]
      · simp [h1]
    · refine ⟨w 0 / v 0, ?_⟩
      ext i
      fin_cases i
      · simp [h0]
      · show w 0 / v 0 * v 1 = w 1
        field_simp
        linear_combination -h
  rw [hCH, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb] at hc
  have c0 : T.trace * (b * w 0) - T.det * (a * v 0) = c * (T.trace * w 0 - T.det * v 0) :=
    congrFun hc 0
  have c1 : T.trace * (b * w 1) - T.det * (a * v 1) = c * (T.trace * w 1 - T.det * v 1) :=
    congrFun hc 1
  by_contra ht
  have hac : a = c := by
    have : T.det * (a - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination w 0 * c1 - w 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left hdet)
  have hbc : b = c := by
    have : T.trace * (b - c) * (v 0 * w 1 - v 1 * w 0) = 0 := by
      linear_combination v 0 * c1 - v 1 * c0
    exact sub_eq_zero.1 ((mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hD)).resolve_left ht)
  subst hac hbc
  have a0 := congrFun ha 0
  have a1 := congrFun ha 1
  have b0 := congrFun hb 0
  have b1 := congrFun hb 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    at a0 a1 b0 b1
  have s00 : S 0 0 = b := by
    apply mul_right_cancel₀ hD
    linear_combination w 1 * a0 - v 1 * b0
  have s01 : S 0 1 = 0 := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b0 - w 0 * a0
  have s11 : S 1 1 = b := by
    apply mul_right_cancel₀ hD
    linear_combination v 0 * b1 - w 0 * a1
  have hp : S.charpoly = (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C b) := by
    rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, s00, s01, s11]
    simp only [map_add (f := _), map_sub, map_mul, map_zero]
    ring
  have hu := hsep.squarefree (Polynomial.X - Polynomial.C b) (hp ▸ dvd_rfl)
  exact Polynomial.not_isUnit_X_sub_C b hu
end

section

theorem UpperTheory.Reformulated.B.DYlb6.main :
    ∀ {R W T : Type} [inst : CommRing R] [inst_1 : AddCommGroup W] [inst_2 : AddCommGroup T] [inst_3 : _root_.Module R T]
      (j : TensorProduct ℤ R W ≃ₗ[R] T),
      Submodule.span R (Set.range fun (a : W) ↦ (j : TensorProduct ℤ R W → T) ((1 : R) ⊗ₜ[ℤ] a)) = ⊤ := by
  intro R W T _ _ _ _ j
  rw [Submodule.eq_top_iff']
  intro t
  obtain ⟨x, rfl⟩ := j.surjective t
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r w =>
    have h : r ⊗ₜ[ℤ] w = r • ((1 : R) ⊗ₜ[ℤ] w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨w, rfl⟩)
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
end

section

theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by
  intro F E _ _ _ h σ α hα x hx
  by_contra hxr
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have li : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hxr
      refine ⟨-(s / t), ?_⟩
      have hst' : algebraMap F E s + algebraMap F E t * x = 0 := by
        simpa [Algebra.smul_def] using hst
      have ht' : algebraMap F E t ≠ 0 := by
        simpa using ht
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst'
    subst ht
    simp only [zero_smul, add_zero, Algebra.smul_def, mul_one] at hst
    exact ⟨by simpa using hst, rfl⟩
  have hspan : Submodule.span F (Set.range ![(1 : E), x]) = ⊤ :=
    li.span_eq_top_of_card_eq_finrank' (by simp [h])
  have hmem : α ∈ Submodule.span F (Set.range ![(1 : E), x]) := by
    rw [hspan]; exact Submodule.mem_top
  refine hα ?_
  clear hα
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    fin_cases i
    · simp
    · simpa using hx
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), ha, hb]
  | smul c a _ ha => rw [map_smul, ha]
end

section

theorem UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place :
    ∀ {M V : Type} [inst : AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℚ V] (j : M →+ V),
    Function.Injective (⇑j : M → V) →
      (∀ (w : V), ∃ (m : ℕ) (u : M), m ≠ (0 : ℕ) ∧ m • w = (j : M → V) u) → Module.finrank ℤ M = Module.finrank ℚ V := by
  intro M V _ _ _ _ _ j hj hs
  classical
  let b := Module.Free.chooseBasis ℤ M
  have h1 : LinearIndependent ℤ (j.toIntLinearMap ∘ b) :=
    b.linearIndependent.map' j.toIntLinearMap (LinearMap.ker_eq_bot.mpr hj)
  have h2 : LinearIndependent ℚ (j.toIntLinearMap ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have key : ∀ u : M, j u ∈ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro u
    have hu : j u = ∑ i, (b.repr u i) • j (b i) := by
      conv_lhs => rw [← b.sum_repr u]

      simp only [map_sum, map_zsmul]
    rw [hu]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have h3 : ⊤ ≤ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro w _
    obtain ⟨m, u, hm, hw⟩ := hs w
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have : w = (m : ℚ)⁻¹ • j u := by
      rw [← hw, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (key u)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (Module.Basis.mk h2 h3)]
end
