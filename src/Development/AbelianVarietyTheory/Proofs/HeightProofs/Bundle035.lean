module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Mathlib.Algebra.Module.StablyFree.Basic
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockBasisMatrix

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_basis (S : HSpace E) (Q : Matrix (Fin S.rank) (Fin S.rank) E) (hQ : IsUnit Q.det) :
    ∃ b : Module.Basis (Fin S.rank) E S.V, Q = S.frame.toMatrix b := by
  refine ⟨S.frame.map (Matrix.toLinearEquiv S.frame Q hQ), ?_⟩
  ext i j
  simp [Module.Basis.toMatrix_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Finsupp.single_apply]

theorem isUnit_det (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) : IsUnit (S.frame.toMatrix b).det := by
  letI := Module.Basis.invertibleToMatrix S.frame b
  exact Matrix.isUnit_det_of_invertible _

theorem gram_change (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i j : Fin S.rank) :
    (((S.frame.toMatrix b).map star)ᵀ * S.gram * S.frame.toMatrix b) i j = S.hT (b i) (b j) := by
  conv_rhs => rw [← S.frame.sum_repr (b i), ← S.frame.sum_repr (b j)]

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram,
  map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
  Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem diag_ne_zero (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (i : Fin S.rank) : S.hT (b i) (b i) ≠ 0 := by
  intro h0
  refine b.ne_zero i (S.nondeg.2 _ fun x => ?_)

  rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  by_cases hk : k = i
  · rw [hk, h0, smul_zero]
  · rw [ho k i hk, smul_zero]

theorem diag_real (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) (x : S.V) :
    (((τ (S.hT x x)).re : ℝ) : ℂ) = τ (S.hT x x) := by
  rw [← Complex.conj_eq_iff_re, ← hτ]
  exact congrArg τ (S.herm.eq x x)

theorem toMatrix_mul_diag (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (s : Module.End E S.V)
    (c : Fin S.rank → E) (hs : ∀ i, s (b i) = c i • b i) :
    LinearMap.toMatrix S.frame S.frame s * S.frame.toMatrix b = S.frame.toMatrix b * Matrix.diagonal c := by
  rw [linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [Matrix.mul_diagonal, LinearMap.toMatrix_apply, hs, Module.Basis.toMatrix_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

theorem orthogonal_basis (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) :
    (∀ i, (τ (S.hT (b i) (b i))).re ≠ 0) ∧
    ((S.frame.toMatrix b).map τ)ᴴ * S.gram.map τ * (S.frame.toMatrix b).map τ =
      Matrix.diagonal (fun i => (((τ (S.hT (b i) (b i))).re : ℝ) : ℂ)) ∧
    ∀ s : Module.End E S.V, (∀ i, s (b i) = if 0 < (τ (S.hT (b i) (b i))).re then b i else -b i) →
      (LinearMap.toMatrix S.frame S.frame s).map τ * (S.frame.toMatrix b).map τ =
        (S.frame.toMatrix b).map τ * Matrix.diagonal (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : ℂ) else -1) := by
  refine ⟨fun i h => ?_, ?_, fun s hs => ?_⟩
  · have := diag_real S τ hτ (b i)
    rw [h, Complex.ofReal_zero] at this
    exact diag_ne_zero S b ho i ((map_eq_zero τ).1 this.symm)
  · have e : ((S.frame.toMatrix b).map τ)ᴴ = (((S.frame.toMatrix b).map star)ᵀ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, hτ]
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    rw [Matrix.map_apply, gram_change]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, diag_real S τ hτ]
    · rw [Matrix.diagonal_apply_ne _ hij, ho i j hij, map_zero]
  · have h := toMatrix_mul_diag S b s (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : E) else -1)
      (fun i => by rw [hs i]; split_ifs <;> simp)
    rw [← Matrix.map_mul, h, Matrix.map_mul, Matrix.diagonal_map (map_zero τ)]
    congr 2
    funext i
    split_ifs <;> simp

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem basis_matrix : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  intro D V
  exact ⟨exists_basis V, fun b => ⟨isUnit_det V b, gram_change V b,
    fun ho τ => orthogonal_basis V b ho (tauE D τ) (tauE_star τ)⟩⟩

end GlobalTheory.FockBasisMatrix
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare.SymplVal

theorem trace_field {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  obtain ⟨a, ha⟩ := hf (e + σ e) (by rw [map_add (f := _), hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h2, map_add (f := _), h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

theorem trace_tensor {F E : Type} [Field F] [Field E] [Algebra F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (hf : ∀ e, σ e = e → ∃ f, algebraMap F E f = e)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h2 σ hσ hf, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
      Algebra.algebraMap_eq_smul_one]

theorem trace_AE (D : D7) (z : AE D) :
    algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) z) = z + cA D z :=
  trace_tensor D.sp.cm.deg2 D.sp.cm.sig (fun e => star_star e) (fun e he => (D.sp.cm.fixed e).1 he) _ z

theorem map_sum4 {A : Type} [CommRing A] (φ : A →+* ℂ) (c : A →+* A) (hc : ∀ a, φ (c a) = starRingEnd ℂ (φ a))
    {m n : ℕ} (x y : Fin m → Fin n → A) (P Q : Fin m → Fin n → Fin m → Fin n → A) :
    φ (∑ i, ∑ j, ∑ k, ∑ l, c (x i j) * P i j k l * Q i j k l * y k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, starRingEnd ℂ (φ (x i j)) * φ (P i j k l) * φ (Q i j k l) * φ (y k l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hc]

theorem comp_hHom {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W) :
    θ τ (infPart D (hHom V W x y)) = hC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  unfold hHom hC
  split_ifs
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram k i)) (fun i j k l => incA D (W.gram j l))).trans ?_
    simp only [hi]
    rfl
  · refine (map_sum4 ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
      (fun i j k l => incA D (V.gram i k)) (fun i j k l => incA D (W.gram l j))).trans ?_
    simp only [hi]
    rfl

theorem valTau_sympl : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V W : HSp D) (τ : D.what₂.Tau) (x y : WA V W),
    valTau θ τ (sympl V W x y) = symplC V W τ (wAt θ V W τ x) (wAt θ V W τ y) := by
  intro D θ hθ V W τ x y
  unfold valTau sympl symplC
  rw [trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul, comp_incA hθ,
    comp_hHom hθ, Complex.add_re, Complex.conj_re, two_mul]

end GlobalTheory.FockCompare.SymplVal
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockCompare.CartanRel

theorem J_mul_J (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_conjTranspose (p q : ℕ) : (Formalism.UG.Jpq p q)ᴴ = Formalism.UG.Jpq p q := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem isKC_iff {p q : ℕ} (b : Mat p q) : IsKC b ↔ b * Formalism.UG.Jpq p q = Formalism.UG.Jpq p q * b := by
  have hJ : Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hJ]
  constructor
  · intro h
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases i with i | i <;> rcases j with j | j
    · simp
    · simp [h (Sum.inl i) (Sum.inr j) (by simp [sameBlock])]
    · simp [h (Sum.inr i) (Sum.inl j) (by simp [sameBlock])]
    · simp
  · intro h i j hij
    have e := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    rcases i with i | i <;> rcases j with j | j
    · simp [sameBlock] at hij
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (-1 / 2 : ℂ) * e
    · simp only [Sum.elim_inl, Sum.elim_inr] at e
      linear_combination (1 / 2 : ℂ) * e
    · simp [sameBlock] at hij

theorem cartan_rel : ∀ (n p q : ℕ), p + q = n → ∀ (A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ) (G t : Matrix (Fin n) (Fin n) ℂ), G.det ≠ 0 → Aᴴ * Formalism.UG.Jpq p q * A = G → Formalism.UG.Jpq p q * A = A * t → IsCart G t ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, (∃ b : Mat p q, IsKC b ∧ b * A = A * g) ↔ Commute g t := by
  intro n p q hn A G t hG hA ht
  have hJ := J_mul_J p q
  have hJc := J_conjTranspose p q
  generalize hJdef : Formalism.UG.Jpq p q = J at hJ hJc hA ht
  obtain ⟨B, hBA, hAB⟩ : ∃ B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ, B * A = 1 ∧ A * B = 1 := by
    have h1 : (G⁻¹ * (Aᴴ * J)) * A = 1 := by
      rw [Matrix.mul_assoc, hA, Matrix.nonsing_inv_mul _ (Ne.isUnit hG)]
    exact ⟨_, h1, (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [hn])).1 h1⟩
  have cancel : ∀ x y : Matrix (Fin n) (Fin n) ℂ, A * x = A * y → x = y := by
    intro x y h
    have := congrArg (B * ·) h
    simpa only [← Matrix.mul_assoc, hBA, Matrix.one_mul] using this
  have hJJ : J * (J * A) = A := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hGt : G * t = Aᴴ * A := by
    rw [← hA, Matrix.mul_assoc, ← ht, Matrix.mul_assoc, hJJ]
  refine ⟨⟨?_, ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  · apply cancel
    rw [← Matrix.mul_assoc, ← ht, Matrix.mul_assoc, ← ht, hJJ, Matrix.mul_one]
  · rw [Matrix.mul_assoc, hGt, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, ← ht,
      Matrix.conjTranspose_mul, hJc, hA]
  · rw [hGt]
    refine Matrix.PosDef.conjTranspose_mul_self A ?_
    intro x y h
    have := congrArg (B.mulVec) h
    simpa only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] using this
  · rintro ⟨b, hb, hbA⟩
    rw [isKC_iff, hJdef] at hb
    apply cancel
    calc A * (g * t) = b * (J * A) := by rw [← Matrix.mul_assoc, ← hbA, Matrix.mul_assoc, ← ht]
      _ = J * (A * g) := by rw [← Matrix.mul_assoc, hb, Matrix.mul_assoc, hbA]
      _ = A * (t * g) := by rw [← Matrix.mul_assoc, ht, Matrix.mul_assoc]
  · intro h
    refine ⟨A * g * B, ?_, ?_⟩
    · rw [isKC_iff, hJdef]
      have hBJ : B * J = t * B := by
        calc B * J = B * (J * A) * B := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_one]
          _ = t * B := by rw [ht, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
      calc A * g * B * J = A * (g * t) * B := by
            rw [Matrix.mul_assoc, hBJ]; simp only [Matrix.mul_assoc]
        _ = A * t * (g * B) := by rw [h.eq]; simp only [Matrix.mul_assoc]
        _ = J * (A * g * B) := by rw [← ht]; simp only [Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, hBA, Matrix.mul_one]

end GlobalTheory.FockCompare.CartanRel
end

section

open GlobalTheory.FockCompare
open scoped ContDiff

namespace GlobalTheory.FockCompare

theorem hD_eq_fderiv {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (f : G → ℂ) (hf : Sm ι f) (u : R) (w : G) :
    hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
      fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  have hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) :=
    ((hf w).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u)))
      (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul] at this
    exact this
  have h0 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * ((om (π w) (t • u) : ℝ) : ℂ))
      (-(Real.pi * Complex.I) * ((om (π w) u : ℝ) : ℂ)) 0 := by
    refine HasDerivAt.const_mul _ (HasDerivAt.ofReal_comp ?_)
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (om (π w) u)
  have h3 := (h0.cexp.mul h2).deriv
  unfold hD
  refine Eq.trans h3 ?_
  simp

theorem hD_formula_smooth : ∀ (G R : Type) [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] (ι : R →+ G) (π : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ), (∀ x, π (ι x) = x) →
    ∀ (f : G → ℂ), Sm ι f → ∀ u : R,
      (∀ w, hD ι π om u f w = -(Real.pi * Complex.I) * (om (π w) u : ℝ) * f w +
        fderiv ℝ (fun x : R => f (w + ι x)) 0 u) ∧ Sm ι (hD ι π om u f) := by
  intro G R _ _ _ _ ι π om hπ f hf u
  refine ⟨hD_eq_fderiv ι π om f hf u, fun w => ?_⟩
  have e : (fun x : R => hD ι π om u f (w + ι x)) = fun x : R =>
      -(Real.pi * Complex.I) * ((om.flip u (π w + x) : ℝ) : ℂ) * f (w + ι x) +
        fderiv ℝ (fun y : R => f (w + ι y)) x u := by
    funext x
    rw [hD_eq_fderiv ι π om f hf, map_add π, hπ, LinearMap.flip_apply]
    congr 2
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add (f := _), add_assoc]
  rw [e]
  have h1 : ContDiff ℝ ∞ fun x : R => (om.flip u (π w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip u)).contDiff.comp (contDiff_const.add contDiff_id)
  refine ContDiff.add (ContDiff.mul (ContDiff.mul contDiff_const
    (Complex.ofRealCLM.contDiff.comp h1)) (hf w)) ?_
  exact ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

end GlobalTheory.FockCompare
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder Topology

namespace GlobalTheory.FockCompare.ThetaCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem infPart_eq_zero (h : Chart θ σ) (a : AE D) (ha : ∀ τ, θ τ (infPart D a) = 0) : infPart D a = 0 := by
  let e : AF D.host.F := ((1 : Ainf D.host.F), (0 : Af D.host.F))
  let E : AE D := e ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D E = 1 := rfl
  have h2 : finPart D E = 0 := by
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  have h3 : infPart D (E * a) = infPart D a := by rw [RingHom.map_mul, h1, one_mul]
  have h4 : E * a = 0 := h.ext _ (by rw [RingHom.map_mul, h2, zero_mul]) fun τ => by rw [h3]; exact ha τ
  rw [← h3, h4, RingHom.map_zero]

theorem continuous_conj : Continuous (cA D) := by
  let f : AE D →ₐ[AF D.host.F] AE D :=
    Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig
  exact IsModuleTopology.continuous_of_linearMap f.toLinearMap

theorem continuous_hHom (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => hHom V W (x t) (y t) := by
  have hx' : ∀ i j, Continuous fun t => cA D (x t i j) := fun i j =>
    continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hx))
  have hy' : ∀ i j, Continuous fun t => y t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hy)
  unfold hHom
  split_ifs <;>
    exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => (((hx' _ _).mul continuous_const).mul continuous_const).mul (hy' _ _)

theorem continuous_symplH (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WA V W} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplH V W (x t) (y t) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul (continuous_hHom V W hy hx)))

theorem continuous_of_level_of_smooth (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (h : Chart θ σ)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (V W : HSp D) (f : WA V W → ℂ)
    (hU : ∃ U : AddSubgroup (WA V W), IsOpen (U : Set (WA V W)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → Heisenberg₂ ψ V W u f = f)
    (hs : Sm (iotaW σ V W) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  have : IsTopologicalAddGroup (AE D) := IsTopologicalRing.isTopologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WA V W) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WA V W → RW V W := fun w' => piW θ V W (w' - w)
  let a : WA V W → WA V W := fun w' => w + iotaW σ V W (x w')
  let u : WA V W → WA V W := fun w' => w' - a w'
  have hx : Continuous x := (continuous_pi' h.inf V W).comp (continuous_id.sub continuous_const)
  have ha : Continuous a := continuous_const.add ((h.continuous_iota V W).comp hx)
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + iotaW σ V W (piW θ V W (w - w))) = 0
    rw [sub_self, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPart D) = 0 := by
    intro w'
    have hp : piW θ V W (u w') = 0 := by
      show piW θ V W (w' - (w + iotaW σ V W (piW θ V W (w' - w)))) = 0
      rw [← sub_sub, AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hg : Continuous fun w' => ψ (-symplH V W (a w') (u w')) * f (a w') :=
    (hψ.comp (continuous_symplH V W ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplH V W (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplH V W (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.FockCompare.ThetaCont

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCompare

theorem smooth_iff_sm_and_real_lines : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (V W : HSp D), (∀ f : WA V W → ℂ, (∀ (k : ℕ) (L : (Fin k → ℝ) →+ WA V W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t)) ↔ Sm (iotaW σ V W) f) ∧ (∀ L : ℝ →+ WA V W, IsRealDir V W L → ∀ t : ℝ, L t = iotaW σ V W (t • piW θ V W (L 1))) ∧ ∀ u : RW V W, ∃ L : ℝ →+ WA V W, IsRealDir V W L ∧ ∀ t : ℝ, L t = iotaW σ V W (t • u) := by
  intro D θ σ h V W
  refine ⟨fun f => ⟨fun H w => ?_, fun H k L hL hL0 w => ?_⟩, fun L hL t => ?_, fun u => ?_⟩
  · let e : RW V W ≃L[ℝ] (Fin (Module.finrank ℝ (RW V W)) → ℝ) :=
      ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_fin_fun])
    have h1 := H _ ((iotaW σ V W).comp e.symm.toLinearEquiv.toLinearMap.toAddMonoidHom)
      ((h.continuous_iota V W).comp e.symm.continuous) (fun t => h.real_iota V W _) w
    have h2 := h1.comp e.contDiff
    have h3 : (fun x : RW V W => f (w + iotaW σ V W x)) = fun x => f (w + iotaW σ V W (e.symm (e x))) := by
      funext x; rw [e.symm_apply_apply]
    rw [h3]
    exact h2
  · let M : (Fin k → ℝ) →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL)
    have h2 := (H w).comp M.contDiff
    have h3 : (fun t => f (w + L t)) = fun t => f (w + iotaW σ V W (piW θ V W (L t))) := by
      funext t; rw [h.iota_pi (hL0 t)]
    rw [h3]
    exact h2
  · let M : ℝ →L[ℝ] RW V W :=
      ((piW θ V W).comp L).toRealLinearMap ((continuous_pi' h.inf V W).comp hL.1)
    have h2 : M (t • (1 : ℝ)) = t • M 1 := M.map_smul t 1
    rw [smul_eq_mul, mul_one] at h2
    have h3 : piW θ V W (L t) = t • piW θ V W (L 1) := h2
    rw [← h3, h.iota_pi (hL.2 t)]
  · let M : ℝ →L[ℝ] RW V W := ContinuousLinearMap.toSpanSingleton ℝ u
    exact ⟨(iotaW σ V W).comp M.toLinearMap.toAddMonoidHom,
      ⟨(h.continuous_iota V W).comp M.continuous, fun t => h.real_iota V W _⟩, fun t => rfl⟩

end GlobalTheory.FockCompare
end
