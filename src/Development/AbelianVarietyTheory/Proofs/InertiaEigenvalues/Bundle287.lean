module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle257
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle262
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle252
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle152
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle264
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

section

noncomputable section

namespace GlobalTheory.SpanIdem

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem map_smul_mulVec {k : ℕ} (c : A) (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((c • M).map (toFr A)).mulVec u = toFr A c • (M.map (toFr A)).mulVec u := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext i j
  simp

theorem map_sum_mulVec {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((∑ i, M i).map (toFr A)).mulVec u = ∑ i, ((M i).map (toFr A)).mulVec u := by
  rw [← Matrix.sum_mulVec]
  congr 1
  exact map_sum (toFr A).mapMatrix M Finset.univ

theorem map_mul_mulVec {k : ℕ} (M N : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((M * N).map (toFr A)).mulVec u = (M.map (toFr A)).mulVec ((N.map (toFr A)).mulVec u) := by
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem map_one_sub_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((1 - M).map (toFr A)).mulVec u = u - (M.map (toFr A)).mulVec u := by
  have : (1 - M).map (toFr A) = 1 - M.map (toFr A) := by
    have h := map_sub (toFr A).mapMatrix 1 M
    rw [map_one] at h
    exact h
  rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem eq_of_mulVec {k : ℕ} {M N : Matrix (Fin k) (Fin k) A}
    (h : ∀ u, (M.map (toFr A)).mulVec u = (N.map (toFr A)).mulVec u) : M = N := by
  have h1 : M.map (toFr A) = N.map (toFr A) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, h]
  exact Matrix.map_injective (IsFractionRing.injective A (FractionRing A)) h1

theorem exists_corner (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A)
    (χ : ℕ → (Γ →* Aˣ)) (π : X)
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A)))
    (hr : 2 ≤ r) (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (hd : IsDecomp (t := t) (rep π) ρ χ e)
    (P : Matrix (Fin r) (Fin r) A) :
    ∃ a, InRing T rep a ∧
      ∀ u, e (((a π).map (toFr A)).mulVec u) = ((P.map (toFr A)).mulVec (e u).1, 0) := by
  obtain ⟨m, f, h, hP, hχ⟩ := GlobalTheory.T.exists_repMatrix_combination_killing_characters ρ χ hr hs P
  refine ⟨∑ k, f k • fun x => mat (rep x) (h k),
    inRing_sum _ fun k _ => inRing_smul _ (inRing_mat _), fun u => ?_⟩

  rw [Finset.sum_apply, map_sum_mulVec, map_sum, ← hP, map_sum_mulVec]
  have key : ∀ k, e ((((f k • fun x => mat (rep x) (h k)) π).map (toFr A)).mulVec u) =
      (((f k • mat ρ (h k)).map (toFr A)).mulVec (e u).1,
        fun c : Fin t => toFr A (f k * ((χ ((c : ℕ) + 1) (h k) : Aˣ) : A)) * (e u).2 c) := by
    intro k
    rw [Pi.smul_apply, map_smul_mulVec, map_smul, ← overK_apply, hd, map_smul_mulVec, overK_apply]
    refine Prod.ext rfl ?_
    funext c
    simp [mul_assoc]
    simp [Algebra.smul_def]
  simp only [key]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
  · rw [Prod.snd_sum]
    funext c
    rw [Finset.sum_apply]

    simp only [← Finset.sum_mul, ← map_sum, hχ, map_zero, zero_mul, Pi.zero_apply]

theorem pow_succ_eval {b : X → Matrix (Fin n) (Fin n) A} {π : X} (h : b π * b π = b π) (k : ℕ) :
    (b ^ (k + 1)) π = b π := by
  rw [Pi.pow_apply]
  exact IsIdempotentElem.pow_succ_eq k h

theorem exists_idem (l : ℕ) [Fact l.Prime] [Finite X] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (b : X → Matrix (Fin n) (Fin n) A) (hb : InRing T rep b) (hπ : b π * b π = b π) :
    ∃ E, InRing T rep E ∧ E * E = E ∧ E π = b π ∧ (∀ y, y * b = 0 → y * E = 0) ∧
      (∀ y, b * y = 0 → E * y = 0) := by
  haveI : Module.Finite ℤ_[l] (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (Module.Finite ℤ_[l] (Fin n → Fin n → A))
  obtain ⟨E, hE, hM⟩ := GlobalTheory.T.exists_idempotent_sub_mem_of_pow_sub_mem' l b
  refine ⟨E, ?_, hE, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := hM ((Subalgebra.toSubmodule (ringR T rep)).restrictScalars ℤ_[l]) 0 fun k => by
      rw [sub_zero]
      exact pow_mem ((mem_ringR T rep b).2 hb) (k + 1)
    rw [sub_zero] at this
    exact (mem_ringR T rep E).1 this
  · have := hM (LinearMap.ker (LinearMap.proj π)) b fun k => by
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply, pow_succ_eval hπ, sub_self]
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply] at this
    exact sub_eq_zero.1 this
  · have := hM (LinearMap.ker (LinearMap.mulLeft ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero, pow_succ', ← mul_assoc, hy, zero_mul]
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero] at this
  · have := hM (LinearMap.ker (LinearMap.mulRight ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero, pow_succ, mul_assoc, hy, mul_zero]
    rwa [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero] at this

theorem rank_single {K : Type} [Field K] (i : Fin r) :
    (Matrix.single i i (1 : K)).rank = 1 := by
  classical
  have : Matrix.single i i (1 : K) = Matrix.diagonal (Pi.single i 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
    grind
  rw [this, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨i, by simp⟩, ?_⟩
  rintro ⟨a, ha⟩
  apply Subtype.ext
  by_contra h
  exact ha (Pi.single_eq_of_ne h 1)

theorem exists_orthogonal_idempotents : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  intro l _ Γ X A _ _ _ _ _ _ n r t T rep ρ χ π e hr hs hd
  obtain ⟨a, ha, hact⟩ := exists_corner T rep ρ χ π e hr hs hd 1
  have hb : ∀ u, e ((((1 - a) π).map (toFr A)).mulVec u) = (0, (e u).2) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hact,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact Prod.ext (by simp) (by simp)
  obtain ⟨eB, hB, hBB, hBπ, -, -⟩ := exists_idem l T rep π (1 - a) (inRing_sub inRing_one ha) (by
    apply eq_of_mulVec
    intro u
    apply e.injective
    rw [map_mul_mulVec, hb, hb])
  rw [← hBπ] at hb
  let i : Fin r := ⟨0, by omega⟩
  obtain ⟨a', ha', hact'⟩ := exists_corner T rep ρ χ π e hr hs hd (Matrix.single i i 1)
  have hε : (Matrix.single i i (1 : A)).map (toFr A) = Matrix.single i i 1 := by
    rw [Matrix.map_single, map_one]
  rw [hε] at hact'
  have hc : ∀ u, e ((((1 - eB) π).map (toFr A)).mulVec u) = ((e u).1, 0) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hb]
    exact Prod.ext (by simp) (by simp)
  have hb' : ∀ u, e (((((1 - eB) * a' * (1 - eB)) π).map (toFr A)).mulVec u) =
      ((Matrix.single i i 1).mulVec (e u).1, 0) := by
    intro u
    rw [Pi.mul_apply, Pi.mul_apply, map_mul_mulVec, map_mul_mulVec, hc, hact', hc]
  have h1 := inRing_sub inRing_one hB
  obtain ⟨e1, h1R, h11, h1π, hl, hrr⟩ := exists_idem l T rep π ((1 - eB) * a' * (1 - eB))
    (inRing_mul (inRing_mul h1 ha') h1) (by
      apply eq_of_mulVec
      intro u
      apply e.injective
      rw [map_mul_mulVec, hb', hb', Matrix.mulVec_mulVec, Matrix.single_mul_single_same, one_mul])
  refine ⟨eB, e1, ⟨hB, h1R, hBB, h11, hl eB ?_, hrr eB ?_⟩, hb, Matrix.single i i 1, rank_single i, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, mul_sub eB 1 eB, mul_one, hBB, sub_self, zero_mul, zero_mul]
  · rw [mul_assoc, sub_mul 1 eB eB, one_mul, hBB, sub_self, mul_zero]
  · rw [h1π]
    exact hb'

end GlobalTheory.SpanIdem

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

theorem isHomogeneous_det_of_linear {σ R : Type} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => M (τ i) i) (fun _ => 1) (fun i _ => h (τ i) i)
  simpa using this

theorem coeff_aeval_of_isHomogeneous {R : Type} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin 2) R) (h : P.IsHomogeneous n) (j : ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1] P).coeff j =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum P]

  rw [map_sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1]
        (MvPolynomial.monomial d (AddMonoidAlgebra.coeff P d))).coeff j =
        if d 0 = j then AddMonoidAlgebra.coeff P d else 0 := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  simp_rw [hterm]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have hd' : AddMonoidAlgebra.coeff P d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have := h hd'
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

theorem coeff_det_pencil_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  intro Γ X O _ _ n T rep hT a b ha hb j
  set c : Fin 2 → X → Matrix (Fin n) (Fin n) O := ![a, b] with hc
  have hcR : ∀ k, InRing T rep (c k) := by
    intro k; fin_cases k
    · exact ha
    · exact hb
  have key := GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hT 2 c hcR
  set P : X → MvPolynomial (Fin 2) O := fun x =>
    Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin 2) O) • (c k x).map MvPolynomial.C) with hP
  have hhom : ∀ x, (P x).IsHomogeneous n := by
    intro x
    refine isHomogeneous_det_of_linear _ fun i j => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X O k).mul (MvPolynomial.isHomogeneous_C (Fin 2) (c k x i j))
  have hdet : ∀ x, Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O))) =
      MvPolynomial.aeval ![(Polynomial.X : Polynomial O), 1] (P x) := by
    intro x
    rw [hP, AlgHom.map_det]
    congr 1
    ext i j
    simp [hc, Fin.sum_univ_two, Matrix.map_apply]
  have hfun : (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O)))).coeff j) =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        (fun x => if d 0 = j then AddMonoidAlgebra.coeff (P x) d else 0) := by
    funext x
    rw [hdet x, coeff_aeval_of_isHomogeneous _ (hhom x) j, Finset.sum_apply]
  rw [hfun]
  refine Subalgebra.sum_mem _ fun d _ => ?_
  by_cases hd : d 0 = j
  · simp only [hd, if_true]
    exact key d
  · simp only [hd, if_false]
    exact T.zero_mem

end GlobalTheory.SpanRing
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem lTensor_iota_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → (∀ (g : GQ l) (x : Bst P), ι (actSt P g x) = P.actQdR g (ι x)) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ (g : ↥(GK K)) (z : V ⊗[ℚ_[l]] Bst P), LinearMap.lTensor V ι.toLinearMap (stRep P ρ g z) = actVdR (P.PD K) ρ g (LinearMap.lTensor V ι.toLinearMap z)) ∧ (∀ w : V ⊗[ℚ_[l]] P.R.B, LinearMap.lTensor V ι.toLinearMap (crisIncl P ℚ_[l] V w) = ιV (P.PD K) (LL := ℚ_[l]) (V := V) w) ∧ ∀ v : V, LinearMap.lTensor V ι.toLinearMap (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) = v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  intro l _ P ι hC hG K V _ _ ρ
  refine ⟨fun g z => ?_, fun w => ?_, fun v => ?_⟩
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [stRep_tmul, actVdR, hG, P.PD_actdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp [crisIncl_tmul, ιV, hC, P.PD_ι]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · simp

end GlobalTheory.InertiaEigenvalues
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem monSt_surjective_onto {l : ℕ} [Fact l.Prime] (P : LocPrime l) :
    Function.Surjective (monSt P) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | monomial n a =>
    have hn : ((n + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    refine ⟨-Polynomial.monomial (n + 1) (((n + 1 : ℕ) : ℚ_[l])⁻¹ • a), ?_⟩
    rw [map_neg, monSt_apply, neg_neg, Polynomial.derivative_monomial, Nat.add_sub_cancel,
      ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem monV_surjective_onto :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V],
      Function.Surjective (monV P ℚ_[l] V) := by
  intro l _ P V _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul v b =>
    obtain ⟨c, rfl⟩ := monSt_surjective_onto P b
    exact ⟨v ⊗ₜ c, monV_tmul P v c⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

end GlobalTheory.PMon
end

section

open Formalism
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_ainf_frobenius_iterate_eq_xi_mul : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e → ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧ (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  first | exact @GlobalTheory.PeriodSol.period_solution | exact GlobalTheory.PeriodSol.period_solution | (intros; apply GlobalTheory.PeriodSol.period_solution <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

theorem resΓ_eq_one_of_chi {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K)))
    (g : ↥(GK K)) (h1 : P.χQ g = 1) : W.resΓ g = 1 := by
  apply W.χΓ_inj
  rw [map_one W.χΓ]
  apply Units.ext
  apply Subtype.ext
  have h3 := W.χΓ_res g
  rw [P.PD_χ, h1, Units.val_one, map_one] at h3
  exact h3

theorem hinf_fixes_εroot_and_resΓ_eq_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l),
    (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧
    ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K,
      ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  intro l _ P AI K
  have hχ : ∀ g ∈ Hinf K, P.χQ g = 1 := fun g hg =>
    ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g
      (IntermediateField.fixingSubgroup_antitone (show K0 K ≤ Kinf K from le_sup_left) hg)).2.1 hg
  refine ⟨fun g hg j => ?_, fun s LL hG W g hg => ?_⟩
  · have := GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g 1 (by simp [hχ g hg]) j
    rwa [pow_one] at this
  · have h1 : Ks K s ≤ Kinf K := by
      apply sup_le_sup_left _ _
      apply IntermediateField.adjoin.mono
      intro x hx
      exact ⟨s, hx⟩
    have h2 : K.1 ≤ Ks K s := hG.2.2.1
    have hgK : g ∈ GK K := IntermediateField.fixingSubgroup_antitone (h2.trans h1) hg
    exact ⟨hgK, resΓ_eq_one_of_chi P W ⟨g, hgK⟩ (hχ g hg)⟩

end GlobalTheory.Decompl
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

theorem _root_.GlobalTheory.T.wachSaturation_image_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  first | exact @GlobalTheory.NL.SatFree.satM_free_and_spans | exact GlobalTheory.NL.SatFree.satM_free_and_spans | (intros; apply GlobalTheory.NL.SatFree.satM_free_and_spans <;> assumption)
end
