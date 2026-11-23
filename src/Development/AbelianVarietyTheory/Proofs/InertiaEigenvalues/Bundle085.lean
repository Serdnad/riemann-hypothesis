module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle032
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle015
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle034
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle036
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by
  first | exact @GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | exact GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix | (intros; apply GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix <;> assumption)
end

section

namespace GlobalTheory.TraceConj

open IsLocalRing

theorem ker_le_ker_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span R (Set.range N) = ⊤) :
    LinearMap.ker (Finsupp.linearCombination R (fun g => M g)) ≤
      LinearMap.ker (Finsupp.linearCombination R (fun g => N g)) := by
  classical
  set a := Finsupp.linearCombination R (fun g => M g) with ha
  set b := Finsupp.linearCombination R (fun g => N g) with hb
  have hab : ∀ c g, (a c * M g).trace = (b c * N g).trace := by
    intro c g
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), add_mul, add_mul, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single x c =>
      simp only [ha, hb, Finsupp.linearCombination_single, Matrix.smul_mul, Matrix.trace_smul, ← map_mul, h]
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have h1 : ∀ Y ∈ Submodule.span R (Set.range N), (b c * Y).trace = 0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨g, rfl⟩ := hY; rw [← hab, hc]; simp
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul t x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
  ext p q
  have := h1 (Matrix.single q p 1) (hN ▸ Submodule.mem_top)
  rw [Matrix.trace_mul_single] at this
  simpa using this

theorem span_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  classical
  let a := Finsupp.linearCombination K (fun g => M g)
  let b := Finsupp.linearCombination K (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have hb : LinearMap.range b = ⊤ := by rw [Finsupp.range_linearCombination]; exact hN
  let f : LinearMap.range a →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker a).liftQ b hker).comp a.quotKerEquivRange.symm.toLinearMap
  have hf : Function.Surjective f := by
    intro Y
    obtain ⟨c, rfl⟩ := LinearMap.range_eq_top.1 hb Y
    refine ⟨a.quotKerEquivRange (Submodule.Quotient.mk c), ?_⟩
    simp [f]
  have hle := LinearMap.finrank_le_finrank_of_surjective hf
  have := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle)
  rwa [Finsupp.range_linearCombination] at this

theorem span_top_of_residual {Γ O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (M : Γ → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  classical
  have lift : ∀ Z ∈ Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)),
      ∃ Y ∈ Submodule.span O (Set.range M), Y.map (residue O) = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ => obtain ⟨g, rfl⟩ := hZ; exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, Submodule.add_mem _ hx hy, by ext; simp⟩
    | smul t x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := residue_surjective t
      exact ⟨t • x, Submodule.smul_mem _ _ hx, by ext; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
    (maximalIdeal_le_jacobson _) fun X _ => ?_
  obtain ⟨Y, hY, hYX⟩ := lift (X.map (residue O)) (h ▸ Submodule.mem_top)
  rw [← add_sub_cancel Y X]
  refine Submodule.add_mem_sup hY ?_
  rw [Matrix.matrix_eq_sum_single (X - Y)]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j ((X - Y) i j) = (X - Y) i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hYX i) j).symm

theorem exists_linearMap_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hM : Submodule.span R (Set.range M) = ⊤) (hN : Submodule.span R (Set.range N) = ⊤) :
    ∃ φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R, φ 1 = 1 ∧ ∀ g X, φ (M g * X) = N g * φ X := by
  classical
  let a := Finsupp.linearCombination R (fun g => M g)
  let b := Finsupp.linearCombination R (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have ha : Function.Surjective a := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]; exact hM
  let φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    ((LinearMap.ker a).liftQ b hker).comp (a.quotKerEquivOfSurjective ha).symm.toLinearMap
  have hφ : ∀ c, φ (a c) = b c := fun c => by
    have : a c = a.quotKerEquivOfSurjective ha (Submodule.Quotient.mk c) := rfl
    rw [this]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hφg : ∀ g, φ (M g) = N g := fun g => by
    simpa [a, b] using hφ (Finsupp.single g 1)
  refine ⟨φ, by simpa using hφg 1, fun g X => ?_⟩
  have hX : X ∈ Submodule.span R (Set.range M) := hM ▸ Submodule.mem_top
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨g', rfl⟩ := hX; rw [← map_mul, hφg, hφg, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add (f := _), map_add (f := _), mul_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mul_smul, map_smul, map_smul, Matrix.mul_smul, hx]

theorem exists_gl_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] (r : ℕ) (ρ ρ' : Γ →* GL (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∀ g, ((ρ' g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace = ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace) → ∃ U : GL (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  intro O _ _ _ _ Γ _ r ρ ρ' hspan htr
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, fun g => Units.ext (Subsingleton.elim _ _)⟩
  let M : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ
  let N : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ'
  let π : Matrix (Fin r) (Fin r) O →* Matrix (Fin r) (Fin r) (ResidueField O) := (residue O).mapMatrix.toMonoidHom
  have hN' : Submodule.span (ResidueField O) (Set.range (π.comp N)) = ⊤ :=
    span_top_of_trace_eq (π.comp N) (π.comp M) (fun g => by
      change ((N g).map (residue O)).trace = ((M g).map (residue O)).trace
      rw [← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace]
      exact congrArg _ (htr g)) hspan
  obtain ⟨φ, h1, hφ⟩ := exists_linearMap_of_trace_eq M N (fun g => (htr g).symm)
    (span_top_of_residual _ hspan) (span_top_of_residual _ hN')
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ : ∃ j, residue O (φ (Matrix.single j j 1) k k) ≠ 0 := by
    by_contra hc
    push Not at hc
    have e : (1 : Matrix (Fin r) (Fin r) O) = ∑ j, Matrix.single j j 1 := (Matrix.sum_single_one).symm
    have := congrArg (fun X : Matrix (Fin r) (Fin r) O => residue O (X k k)) h1

    rw [e, map_sum, ← e] at this
    simp [Matrix.sum_apply, hc] at this
  let A : Matrix (Fin r) (Fin r) O := Matrix.of fun p q => φ (Matrix.single q j 1) p k
  have hA : ∀ g, N g * A = A * M g := by
    intro g
    ext p q
    have e : M g * Matrix.single q j 1 = ∑ t, M g t q • Matrix.single t j (1 : O) := by
      ext a b
      by_cases hb : j = b
      · subst hb; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, hb]
    have := congrFun (congrFun (hφ g (Matrix.single q j 1)) p) k

    rw [e, map_sum] at this
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, A, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  refine GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top O Γ r ρ ρ' hspan ⟨A, fun h0 => ?_, hA⟩
  refine GlobalTheory.det_ne_zero_of_intertwines_of_span_eq_top _ (fun g => (N g).map (residue O)) hspan
    (A.map (residue O)) k j hj (fun g => ?_) ?_
  · rw [← Matrix.map_mul, hA, Matrix.map_mul]; rfl
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.TraceConj
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  first | exact @GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | exact GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | (intros; apply GlobalTheory.gl_factor_fromBlocks_mod_uniformizer <;> assumption)
end

section

noncomputable section

open Matrix

namespace GlobalTheory.IndexTranspose

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

abbrev stdLat (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) : Submodule O (Fin r → K) :=
  Submodule.span O (Set.range (Pi.basisFun K (Fin r)))

theorem mem_stdLat {v : Fin r → K} :
    v ∈ stdLat O K r ↔ ∃ w : Fin r → O, v = fun i => algebraMap O K (w i) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  · rintro ⟨w, rfl⟩
    refine ⟨w, funext fun i => ?_⟩
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]

def latOf (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : Submodule O (Fin r → K) :=
  (stdLat O K r).map ((A.mulVecLin).restrictScalars O)

theorem mem_latOf {A : Matrix (Fin r) (Fin r) K} {v : Fin r → K} :
    v ∈ latOf O A ↔ ∃ w ∈ stdLat O K r, A *ᵥ w = v := by
  simp [latOf, Submodule.mem_map]

theorem latOf_mul (A B : Matrix (Fin r) (Fin r) K) :
    latOf O (A * B) = (latOf O B).map ((A.mulVecLin).restrictScalars O) := by
  ext v
  rw [Submodule.mem_map, mem_latOf]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨B *ᵥ w, mem_latOf.2 ⟨w, hw, rfl⟩, by simp [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hu
    exact ⟨w, hw, by simp [Matrix.mulVec_mulVec]⟩

theorem latOf_one : latOf O (1 : Matrix (Fin r) (Fin r) K) = stdLat O K r := by
  ext v
  rw [mem_latOf]
  simp

theorem map_mulVec_mem (N : Matrix (Fin r) (Fin r) O) {v : Fin r → K} (hv : v ∈ stdLat O K r) :
    (N.map (algebraMap O K)) *ᵥ v ∈ stdLat O K r := by
  obtain ⟨w, rfl⟩ := mem_stdLat.1 hv
  refine mem_stdLat.2 ⟨N *ᵥ w, funext fun i => ?_⟩
  exact (RingHom.map_mulVec (algebraMap O K) N w i).symm

theorem latOf_unimod (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    latOf O (N.map (algebraMap O K)) = stdLat O K r := by
  apply le_antisymm
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_latOf.1 hv
    exact map_mulVec_mem N hw
  · intro v hv
    refine mem_latOf.2 ⟨(N⁻¹).map (algebraMap O K) *ᵥ v, map_mulVec_mem _ hv, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hN,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem det_map_ne_zero (N : Matrix (Fin r) (Fin r) O) (hN : IsUnit N.det) :
    (N.map (algebraMap O K)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (hN.map _).ne_zero

theorem toAddSubgroup_map (A : Matrix (Fin r) (Fin r) K) (p : Submodule O (Fin r → K)) :
    (p.map ((A.mulVecLin).restrictScalars O)).toAddSubgroup =
      p.toAddSubgroup.map A.mulVecLin.toAddMonoidHom := by
  ext v
  simp [Submodule.mem_map, AddSubgroup.mem_map]

def idx (O : Type) [CommRing O] [Algebra O K] (A : Matrix (Fin r) (Fin r) K) : ℕ :=
  (latOf O A).toAddSubgroup.relIndex (stdLat O K r).toAddSubgroup

theorem idx_mul_right (A U : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) :
    idx O (A * U) = idx O A := by
  unfold idx
  rw [latOf_mul, hU]
  rfl

theorem idx_mul_left (U A : Matrix (Fin r) (Fin r) K) (hU : latOf O U = stdLat O K r) (hd : U.det ≠ 0) :
    idx O (U * A) = idx O A := by
  have hinj : Function.Injective U.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hd hab
  have e : (stdLat O K r).toAddSubgroup = (stdLat O K r).toAddSubgroup.map U.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map]
    exact congrArg Submodule.toAddSubgroup hU.symm
  unfold idx
  rw [latOf_mul, toAddSubgroup_map]
  conv_lhs => rw [e]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj

theorem idx_transpose [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]
    (g : Matrix (Fin r) (Fin r) K) (hg : g.det ≠ 0) : idx O gᵀ = idx O g := by
  classical
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin r × Fin r)) (fun ij => g ij.1 ij.2)
  have hc' := fun ij : Fin r × Fin r => RingHom.mem_rangeS.1 (hc ij (Finset.mem_univ ij))
  choose N0 hN0 using hc'
  set a : K := algebraMap O K (c : O) with ha_def
  have ha : a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors c.2
  let N : Matrix (Fin r) (Fin r) O := Matrix.of fun i j => N0 (i, j)
  have hNmap : N.map (algebraMap O K) = a • g := by
    ext i j
    simp only [N, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hN0 (i, j), ha_def, smul_eq_mul, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
  have hNdet : N.det ≠ 0 := by
    intro h0
    have e := RingHom.map_det (algebraMap O K) N
    rw [h0, map_zero, RingHom.mapMatrix_apply, hNmap, Matrix.det_smul] at e
    exact mul_ne_zero (pow_ne_zero _ ha) hg e.symm
  obtain ⟨P, Q, hP, hQ, d, hPQ⟩ := GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal N hNdet
  set D : Matrix (Fin r) (Fin r) K := a⁻¹ • Matrix.diagonal (fun i => algebraMap O K (d i)) with hD
  have hmap := congrArg (fun M : Matrix (Fin r) (Fin r) O => M.map (algebraMap O K)) hPQ
  simp only [Matrix.map_mul, hNmap, Matrix.diagonal_map (map_zero _)] at hmap
  have key : g * Q.map (algebraMap O K) = P.map (algebraMap O K) * D := by
    rw [hD, Matrix.mul_smul, ← hmap, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ha, one_smul]
  have hDT : Dᵀ = D := by
    rw [hD, Matrix.transpose_smul, Matrix.diagonal_transpose]
  have hQT : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hPT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have e1 : idx O g = idx O D := by
    rw [← idx_mul_right g _ (latOf_unimod Q hQ), key,
      idx_mul_left _ _ (latOf_unimod P hP) (det_map_ne_zero P hP)]
  have e2 : idx O gᵀ = idx O D := by
    have hQ' := latOf_unimod (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQ'
    have hP' := latOf_unimod (K := K) Pᵀ hPT
    rw [Matrix.transpose_map] at hP'
    have hQd := det_map_ne_zero (K := K) Qᵀ hQT
    rw [Matrix.transpose_map] at hQd
    rw [← idx_mul_left _ gᵀ hQ' hQd, ← Matrix.transpose_mul, key, Matrix.transpose_mul, hDT,
      idx_mul_right _ _ hP']
  rw [e1, e2]

theorem relIndex_transpose_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (h : GL (Fin r) K), ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map ((((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ.mulVecLin).restrictScalars O)).toAddSubgroup.relIndex (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup = (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).toAddSubgroup.relIndex ((Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)).toAddSubgroup := by
  intro O K _ _ _ _ _ _ _ r h
  set g : Matrix (Fin r) (Fin r) K := ((h⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) with hg_def
  set hM : Matrix (Fin r) (Fin r) K := (h : Matrix (Fin r) (Fin r) K) with hM_def
  have hgh : g * hM = 1 := Units.inv_mul h
  have hg : g.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hgh
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at e
    exact zero_ne_one e
  have hginj : Function.Injective g.mulVecLin.toAddMonoidHom :=
    fun a b hab => Matrix.mulVec_injective_of_det_ne_zero hg hab
  change idx O gᵀ = (stdLat O K r).toAddSubgroup.relIndex (latOf O hM).toAddSubgroup
  have e1 : (latOf O g).toAddSubgroup = (stdLat O K r).toAddSubgroup.map g.mulVecLin.toAddMonoidHom :=
    toAddSubgroup_map g _
  have e2 : (stdLat O K r).toAddSubgroup = (latOf O hM).toAddSubgroup.map g.mulVecLin.toAddMonoidHom := by
    rw [← toAddSubgroup_map, ← latOf_mul, hgh, latOf_one]
  rw [idx_transpose g hg, ← AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← e1, ← e2]
  rfl

end GlobalTheory.IndexTranspose
end
end

section

open TensorProduct Module

theorem _root_.GlobalTheory.T.tensorProduct_basis_coordinates : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  first | exact @GlobalTheory.tensorBasisCoords | exact GlobalTheory.tensorBasisCoords | (intros; apply GlobalTheory.tensorBasisCoords <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.isNilpotent_residue_toMatrix_mulLeft' : ∀ (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] [Algebra R S] (n : ℕ) (b : Module.Basis (Fin n) R S) (t : S), t ∈ IsLocalRing.maximalIdeal S → IsNilpotent ((LinearMap.toMatrix b b (LinearMap.mulLeft R t)).map (IsLocalRing.residue R)) := by
  first | exact @GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | exact GlobalTheory.isNilpotent_residue_toMatrix_mulLeft | (intros; apply GlobalTheory.isNilpotent_residue_toMatrix_mulLeft <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_eq_sum_trace_of_trace_like_pi_matrix : ∀ (k : Type) [Field k] (N : ℕ) (n : Fin N → ℕ) (τ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₗ[k] k), (∀ x y, τ (x * y) = τ (y * x)) → ∃ c : Fin N → k, ∀ x, τ x = ∑ i, c i * (x i).trace := by
  first | exact @GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | exact GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace | (intros; apply GlobalTheory.centralLinearForm_pi_matrix_eq_sum_trace <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_algHom_trace_eq_sum_mul_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ), ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k, ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  first | exact @GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | exact GlobalTheory.exists_algHom_trace_eq_sum_mult_trace | (intros; apply GlobalTheory.exists_algHom_trace_eq_sum_mult_trace <;> assumption)
end

section


theorem _root_.GlobalTheory.T.module_finite_quotient_of_complete_of_span_mod_range : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → ∀ {T Z : Type} [AddCommGroup T] [Module R T] [AddCommGroup Z] [Module R Z], (∀ x : ℕ → T, ∃ y : T, ∀ n : ℕ, ∃ z : T, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) → (∀ c : Z, (∀ n : ℕ, ∃ z : Z, c = ϖ ^ n • z) → c = 0) → ∀ (d : T →ₗ[R] Z) (N : Submodule R Z), LinearMap.range d ≤ N → ∀ s : Finset Z, (∀ c : Z, ∃ (a : Z → R) (c' : Z) (x : T), c = ∑ i ∈ s, a i • i + ϖ • c' + d x) → Module.Finite R (Z ⧸ N) := by
  first | exact @GlobalTheory.finite_quotient_of_complete_nakayama | exact GlobalTheory.finite_quotient_of_complete_nakayama | (intros; apply GlobalTheory.finite_quotient_of_complete_nakayama <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.span_image_semilinear_lattice_eq : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V'), (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ S : Set V, Submodule.span O (iV '' (Submodule.span (𝓞 K) S : Set V)) = Submodule.span O (iV '' S) := by
  first | exact @GlobalTheory.span_image_span_eq_of_integral | exact GlobalTheory.span_image_span_eq_of_integral | (intros; apply GlobalTheory.span_image_span_eq_of_integral <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.fg_inf_sup_of_isCompl' : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (A : Submodule (𝓞 K) V) (U U' : Submodule K V), A.FG → IsCompl U U' → (U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K))).FG := by
  first | exact @GlobalTheory.fg_inf_sup_of_isCompl | exact GlobalTheory.fg_inf_sup_of_isCompl | (intros; apply GlobalTheory.fg_inf_sup_of_isCompl <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.intCast_trace_eq_trace_quotient_of_mem' : ∀ (L : Type) [Field L] [NumberField L] (l b : ℕ) [Fact l.Prime] (I Q : Ideal (𝓞 L)), I ⊔ Q = ⊤ → I * Q = Ideal.span {((l ^ b : ℕ) : 𝓞 L)} → ∀ [Algebra (ZMod (l ^ b)) (𝓞 L ⧸ I)] (x : 𝓞 L), x ∈ Q → ((Algebra.trace ℤ (𝓞 L) x : ℤ) : ZMod (l ^ b)) = Algebra.trace (ZMod (l ^ b)) (𝓞 L ⧸ I) (Ideal.Quotient.mk I x) := by
  first | exact @GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | exact GlobalTheory.intCast_trace_eq_trace_quotient_of_mem | (intros; apply GlobalTheory.intCast_trace_eq_trace_quotient_of_mem <;> assumption)
end
