module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

@[expose] public section

section

noncomputable def UpperTheory.Reformulated.B.product_first_partition.blockEmb.{u_1, u_2} :
    (K : Type u_1) →
      [inst : CommRing K] →
        {S : Type u_2} → {k n : ℕ} → S → MvPolynomial (Fin k × Fin n) K →ₐ[K] MvPolynomial (S × Fin k × Fin n) K :=
    fun (K : Type u_1) [CommRing K] {S : Type u_2} {k n : ℕ} (s : S) ↦ MvPolynomial.rename fun (v : Fin k × Fin n) ↦ (s, v)

noncomputable def UpperTheory.Reformulated.B.product_first_partition.tensorLat.{u_1, u_2, u_3} :
    (R : Type u_1) →
      (K : Type u_2) →
        [inst : CommRing R] →
          [inst_1 : CommRing K] →
            [inst_2 : Algebra R K] →
              {S : Type u_3} →
                [Fintype S] →
                  {k n : ℕ} →
                    (S → Submodule R (MvPolynomial (Fin k × Fin n) K)) → Submodule R (MvPolynomial (S × Fin k × Fin n) K) :=
    fun (R : Type u_1) (K : Type u_2) [CommRing R] [CommRing K] [Algebra R K] {S : Type u_3} [Fintype S] {k n : ℕ}
        (M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) ↦
      Submodule.span R
        {P : MvPolynomial (S × Fin k × Fin n) K |
          ∃ (F : S → MvPolynomial (Fin k × Fin n) K),
            (∀ (s : S), F s ∈ M s) ∧
              P =
                ∏ s : S,
                  (UpperTheory.Reformulated.B.product_first_partition.blockEmb K s : MvPolynomial (Fin k × Fin n) K → MvPolynomial (S × Fin k × Fin n) K)
                    (F s)}

private theorem UpperTheory.Reformulated.B.product_first_partition.span_mul_eq {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (M N : Submodule R A) :
    Submodule.span R {X : A | ∃ F ∈ M, ∃ G ∈ N, X = F * G} = M * N := by
  rw [Submodule.mul_def]
  congr 1
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_mul, SetLike.mem_coe, eq_comm]

private theorem UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq {R K : Type} [CommRing R] [CommRing K] [Algebra R K]
    {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}
    (N : S → Submodule R (MvPolynomial (Fin k × Fin n) K)) :
    UpperTheory.Reformulated.B.product_first_partition.tensorLat R K N =
      ∏ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap := by
  have h : ∀ s : S, (N s).map ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap =
      Submodule.span R (((N s).map
        ((UpperTheory.Reformulated.B.product_first_partition.blockEmb K s).restrictScalars R).toLinearMap : Submodule R _) : Set _) :=
    fun s => (Submodule.span_eq _).symm
  rw [Finset.prod_congr rfl fun s _ => h s, Submodule.prod_span]
  unfold UpperTheory.Reformulated.B.product_first_partition.tensorLat
  congr 1
  ext P
  rw [Set.mem_fintype_prod]
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨fun s => UpperTheory.Reformulated.B.product_first_partition.blockEmb K s (F s), fun s => ⟨F s, hF s, rfl⟩, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    choose F hF hFg using hg
    exact ⟨F, hF, Finset.prod_congr rfl fun s _ => (hFg s).symm⟩

theorem UpperTheory.Reformulated.B.product_first_partition.tensor_onto :
    ∀ {R K : Type} [inst : CommRing R] [inst_1 : Field K] [inst_2 : Algebra R K] {S : Type} [inst_3 : Fintype S]
      [DecidableEq S] {k n : ℕ} (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K)),
      (∀ (s : S), M s ≤ Submodule.span R {X : MvPolynomial (Fin k × Fin n) K | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) →
        UpperTheory.Reformulated.B.product_first_partition.tensorLat R K M ≤
          Submodule.span R
            {X : MvPolynomial (S × Fin k × Fin n) K |
              ∃ P ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K A, ∃ Q ∈ UpperTheory.Reformulated.B.product_first_partition.tensorLat R K B, X = P * Q} := by
  intro R K _ _ _ S _ _ k n A B M h
  rw [UpperTheory.Reformulated.B.product_first_partition.span_mul_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq,
    UpperTheory.Reformulated.B.product_first_partition.tensorLat_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod' fun s _ => ?_
  rw [← Submodule.map_mul]
  refine Submodule.map_mono ?_
  rw [← UpperTheory.Reformulated.B.product_first_partition.span_mul_eq]
  exact h s
end

section

theorem UpperTheory.Reformulated.B.Qh20.hfs_aeval_restrict :
    ∀ {L W : Type} [inst : Field L] [inst_1 : AddCommGroup W]
    [inst_2 : _root_.Module L W] (f : Module.End L W) {p : Submodule L W} (h : ∀ x ∈ p, (f : W → W) x ∈ p)
    (q : Polynomial L) (x : ↥p),
    (↑(((Polynomial.aeval (LinearMap.restrict f h) : Polynomial L → ↥p →ₗ[L] ↥p) q : ↥p → ↥p) x) : W) =
      ((Polynomial.aeval f : Polynomial L → Module.End L W) q : W → W) (↑x : W) := by
  intro L W _ _ _ f p h q x
  have hpow : ∀ (n : ℕ) (y : p), ((((LinearMap.restrict f h) ^ n) y : p) : W) = (f ^ n) (y : W) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      rfl
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, hpow]
end

section

theorem UpperTheory.Reformulated.B.Qe22.aeval_inter :
    ∀ {M N : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M]
    [inst_2 : AddCommGroup N] [inst_3 : _root_.Module ℂ N] (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N),
    (∀ (x : M), (f : M → N) ((T : M → M) x) = (T' : N → N) ((f : M → N) x)) →
      ∀ (p : Polynomial ℂ) (x : M),
        (f : M → N) (((Polynomial.aeval T : Polynomial ℂ → Module.End ℂ M) p : M → M) x) =
          ((Polynomial.aeval T' : Polynomial ℂ → Module.End ℂ N) p : N → N) ((f : M → N) x) := by
  intro M N _ _ _ _ f T T' h p
  have hpow : ∀ (n : ℕ) (x : M), f ((T ^ n) x) = (T' ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro x
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hpow]
end

section

theorem UpperTheory.Reformulated.B.Qj10.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p y
  have hpow : ∀ (n : ℕ) (x : Y), ψ ((A ^ n) x) = (B ^ n) (ψ x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

section

theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

section

noncomputable def UpperTheory.Reformulated.B.Qh60.Pz :
    {R : Type} → [inst : Ring R] → [Algebra ℝ R] → R → Prop :=
    fun {R : Type} [Ring R] [Algebra ℝ R] (t : R) ↦
      ∃ (s : Finset ℝ),
        (∀ l ∈ s, (0 : ℝ) < l) ∧
          (Polynomial.aeval t : Polynomial ℝ → R) (∏ l ∈ s, (Polynomial.X - (Polynomial.C : ℝ → Polynomial ℝ) l)) = (0 : R)

private theorem UpperTheory.Reformulated.B.Qh60.aux {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ x : W, x ≠ 0 → 0 < inner ℝ (T x) x := by
  classical
  have hn : Module.finrank ℝ W = Module.finrank ℝ W := rfl
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have hev : ∀ i, Module.End.HasEigenvector T (μ i) (b i) := fun i => by
    simpa using hT.hasEigenvector_eigenvectorBasis hn i
  have happ : ∀ i, T (b i) = μ i • b i := fun i => (hev i).apply_eq_smul
  have hne : ∀ i, b i ≠ 0 := fun i => (hev i).2
  have haev : ∀ (s : Finset ℝ) i,
      (Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))) (b i)
        = (∏ l ∈ s, (μ i - l)) • b i := fun s i => by
    rw [Module.End.aeval_apply_of_hasEigenvector (hev i)]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨s, hs, h0⟩ x hx
    have hpos : ∀ i, 0 < μ i := fun i => by
      have h1 := haev s i
      rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
      obtain ⟨l, hl, h2⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_right (hne i))
      rw [sub_eq_zero.1 h2]
      exact hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (b i), happ i, real_inner_smul_right, real_inner_comm (b i) x]
      ring
    have hex : ∃ i, inner ℝ (b i) x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← b.sum_repr' x]
      simp [hc]
    obtain ⟨i, hi⟩ := hex
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hpos i) (by positivity)⟩
  · intro h
    refine ⟨Finset.univ.image μ, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      have h1 := h (b i) (hne i)
      rw [happ i, real_inner_smul_left] at h1
      exact (pos_iff_pos_of_mul_pos h1).2 (real_inner_self_pos.2 (hne i))
    · refine b.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, haev, LinearMap.zero_apply,
        Finset.prod_eq_zero (Finset.mem_image_of_mem μ (Finset.mem_univ i)) (sub_self _), zero_smul]

theorem UpperTheory.Reformulated.B.Qh60.Pz_iff_pos :
    ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : _root_.Module ℝ W] [FiniteDimensional ℝ W] (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ),
      (∀ (x y : W), ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) y : W → ℝ) x) →
        (∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) x) →
          ∀ (T : Module.End ℝ W),
            (∀ (x y : W),
                ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) ((T : W → W) y)) →
              (UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) x) := by
  intro W _ _ _ Q hsymm hpos T hT
  let c : InnerProductSpace.Core ℝ W :=
    { inner := fun x y => Q x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hpos x h).ne' hx }
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ c
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore c.toCore
  exact UpperTheory.Reformulated.B.Qh60.aux T (fun x y => hT x y)
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp10.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp10.aeval_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp10.Mat C N) (μ : C) (v : Fin N → C),
      Matrix.mulVec y v = μ • v →
        ∀ (Q : Polynomial C),
          Matrix.mulVec ((Polynomial.aeval y : Polynomial C → UpperTheory.Reformulated.B.Qp10.Mat C N) Q) v = Polynomial.eval μ Q • v := by
  intro C _ N y μ v h Q
  have hpow : ∀ n : ℕ, Matrix.mulVec (y ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def,
      Matrix.smul_mulVec, hpow, smul_smul]
end

section

open IsLocalRing in
private lemma finite_of_isFiniteLength {S : Type} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] {M : Type} [AddCommGroup M] [Module S M]
    (h : IsFiniteLength S M) : Finite M := by
  induction h with
  | of_subsingleton => exact Finite.of_subsingleton
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
    have hIm : I = maximalIdeal S := IsLocalRing.eq_maximalIdeal hI
    subst hIm
    haveI : Finite (S ⧸ maximalIdeal S) := ‹Finite (ResidueField S)›
    haveI : Finite (M ⧸ N) := Finite.of_equiv _ e.symm.toEquiv
    haveI : Finite (M ⧸ N.toAddSubgroup) := ‹Finite (M ⧸ N)›
    haveI : Finite N.toAddSubgroup := ih
    exact Finite.of_addSubgroup_quotient N.toAddSubgroup

open IsLocalRing in
theorem UpperTheory.monic_ideal_completion :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
        [IsLocalHom (algebraMap O R)]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (J : Ideal R) (hJ : ∀ x : R, ∃ P : Polynomial O, P.Monic ∧ Polynomial.aeval x P ∈ J)
        (ϖ : O) (hϖ : Irreducible ϖ),
        Finite (R ⧸ (J ⊔ Ideal.span {algebraMap O R ϖ})) := by
  intro O R _ _ _ _ _ _ _ _ _ hres J hJ ϖ hϖ
  obtain ⟨I, hIdef⟩ : ∃ I, I = J ⊔ Ideal.span {algebraMap O R ϖ} := ⟨_, rfl⟩
  rw [← hIdef]
  have hJI : J ≤ I := hIdef ▸ le_sup_left
  have hϖI : algebraMap O R ϖ ∈ I :=
    hIdef ▸ (le_sup_right : _ ≤ J ⊔ Ideal.span {algebraMap O R ϖ}) (Ideal.subset_span rfl)
  by_cases hI : I = ⊤
  · subst hI
    haveI : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Finite.of_subsingleton
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : Algebra.IsIntegral O (R ⧸ I) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, hP, hx⟩ := hJ x
    refine ⟨P, hP, ?_⟩
    rw [← Polynomial.aeval_def]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ O I) x P
    rw [Ideal.Quotient.mkₐ_eq_mk] at h
    rw [h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hJI hx)⟩
  have hm : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_zero_iff.mpr fun Q hQ =>
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) Q (by
      have hle : Ideal.span {ϖ} ≤ Q.comap (algebraMap O (R ⧸ I)) := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
        have : algebraMap O (R ⧸ I) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hϖI
        rw [this]
        exact Q.zero_mem
      have hne : Q.comap (algebraMap O (R ⧸ I)) ≠ ⊤ := (Ideal.comap_isPrime _ Q).ne_top
      change (Q.comap (algebraMap O (R ⧸ I))).IsMaximal
      rw [← hm.eq_of_le hne hle]
      exact hm)
  haveI : IsArtinianRing (R ⧸ I) :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hmk : ∀ x ∈ maximalIdeal R, Ideal.Quotient.mk I x ∈ maximalIdeal (R ⧸ I) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hz
    have h1 := hImax hz
    have h2 : x * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hx
    have h3 : (1 : R) ∈ maximalIdeal R := by
      have := (maximalIdeal R).sub_mem h2 h1
      simpa using this
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
  let φ : O →+* ResidueField (R ⧸ I) := (residue (R ⧸ I)).comp (algebraMap O (R ⧸ I))
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hres x
    refine ⟨a, ?_⟩
    have h := hmk _ ha
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at h
    exact h.symm
  have hφk : ∀ a ∈ maximalIdeal O, φ a = 0 := by
    intro a ha
    have h1 : algebraMap O R a ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun hu => ha (isUnit_of_map_unit (algebraMap O R) a hu)
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmk _ h1)
  haveI : Finite (O ⧸ maximalIdeal O) := ‹Finite (ResidueField O)›
  haveI : Finite (ResidueField (R ⧸ I)) :=
    Finite.of_surjective (Ideal.Quotient.lift (maximalIdeal O) φ hφk)
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφs)
  exact finite_of_isFiniteLength (S := R ⧸ I) (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
end

section

theorem UpperTheory.Reformulated.B.Yra8.main.{u_1, u_2} :
    ∀ {R : Type u_1} {ι : Type u_2} [inst : CommRing R] (s : Finset ι) (e : ι → ℕ) (g : ι → Polynomial R) (c : ι → R),
      (∀ (i : ι), (g i).natDegree ≤ (1 : ℕ)) →
        (∀ (i : ι), (g i).coeff (1 : ℕ) = c i) →
          (∏ i ∈ s, g i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧ (∏ i ∈ s, g i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, c i ^ e i := by
  intro R ι _ s e g c hd hc
  classical
  have hp : ∀ i, (g i ^ e i).natDegree ≤ e i ∧ (g i ^ e i).coeff (e i) = c i ^ e i := by
    intro i
    refine ⟨?_, ?_⟩
    · calc (g i ^ e i).natDegree ≤ e i * (g i).natDegree := Polynomial.natDegree_pow_le
        _ ≤ e i * 1 := Nat.mul_le_mul_left _ (hd i)
        _ = e i := by simp
    · have := Polynomial.coeff_pow_of_natDegree_le (m := e i) (hd i)
      simpa [hc i] using this
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp a).1 ih.1)
    · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hp a).1 ih.1, (hp a).2, ih.2]
end
