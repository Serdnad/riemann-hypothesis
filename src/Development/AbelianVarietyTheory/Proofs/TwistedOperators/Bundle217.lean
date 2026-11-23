module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle206
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
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ArchUniq
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

def trPairL {κ : Type} [Fintype κ] (z : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
    (∑ i, (LinearMap.mulLeft ℝ (z i)).comp (LinearMap.proj i))

theorem trPairL_apply {κ : Type} [Fintype κ] (z w : κ → mixedEmbedding.mixedSpace F) :
    trPairL z w = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * w i) := by
  simp [trPairL, LinearMap.sum_apply]

theorem fderiv_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ)
    (z v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (⇑f) z v = ∑ j, (b.repr v j : ℂ) * fderiv ℝ (⇑f) z (b j) := by
  calc fderiv ℝ (⇑f) z v = fderiv ℝ (⇑f) z (∑ j, b.repr v j • b j) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]

theorem mult_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (y : κ → AF F)
    (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) * mult F (liftV (b j)) z := by
  have h1 : ∀ w : κ → AF F, trForm F w z = trPairL z (fun i => evI F (w i)) := by
    intro w
    rw [trForm_apply, trPairL_apply]
  have h2 : trPairL z (fun i => evI F (y i)) =
      ∑ j, b.repr (fun i => evI F (y i)) j * trPairL z (b j) := by
    calc trPairL z (fun i => evI F (y i))
        = trPairL z (∑ j, b.repr (fun i => evI F (y i)) j • b j) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
  have h3 : ∀ j, (fun i => evI F (liftV (F := F) (b j) i)) = b j := fun j => Coord.loc_lift (b j)
  simp only [mult_apply, h1, h3, h2]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.HeisDerivSpan

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_eq {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f g : SInf F (Fin n × Fin d))
    (hg : ActsD (evI F) (M.heisLine ψ u) f g) :
    g = heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f := by
  ext y
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hr := hR f
  set x : Fin n × Fin d → AF F := liftV y with hx
  have hd1 := hg R hr x
  have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
  have huniq := hd1.unique hd2
  have hRx : R x = R 0 := by
    have := hr.1 0 x (at_liftV y)
    rwa [zero_add] at this
  have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
  simp only [tens, hlx, hRx] at huniq
  exact mul_right_cancel₀ hR0 huniq

theorem heisLine_deriv_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  let b := Module.finBasis ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  set N := Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  let A : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (LineDeriv.lineDerivOpCLM ℂ (SInf F (Fin n × Fin d)) (b j)).toLinearMap
  let B : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (SchwartzMap.smulLeftCLM ℂ (⇑(mult F (liftV (b j))))).toLinearMap
  refine ⟨N + N, fun i => Sum.elim A B (finSumFinEquiv.symm i), fun u _ => ?_⟩
  refine ⟨heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2, fun f f₁ =>
    ⟨actsD_heisLine_eq M ψ hψ u f f₁, fun h => by subst h; exact actsD_heisLine_heisD M ψ hψ u f⟩, fun f => ?_⟩
  set S := Submodule.span ℂ (Set.range fun i => Sum.elim A B (finSumFinEquiv.symm i) f) with hS
  have hA : ∀ j, A j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inl j), by simp only [Equiv.symm_apply_apply, Sum.elim_inl]⟩
  have hB : ∀ j, B j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inr j), by simp only [Equiv.symm_apply_apply, Sum.elim_inr]⟩
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hv
  set y := (M.co.e u).2 with hy
  have key : heisD F v y f = ∑ j, (b.repr v j : ℂ) • A j f +
      ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) • B j f := by
    ext z
    rw [heisD_apply, fderiv_basis b f z v, mult_basis b y z, Finset.sum_mul]
    simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, A, B,
      ContinuousLinearMap.coe_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (mult F (liftV (F := F) (b j))).hasTemperateGrowth]
    simp only [smul_eq_mul]
    ring
  rw [key]
  exact add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hA j))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB j))

end GlobalTheory.HeisDerivSpan
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblNab

open Matrix

section Generic

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def blkN (N : Matrix ι ι A) : Matrix (ι ⊕ ι) (ι ⊕ ι) A := fromBlocks (1 + N) N (-N) (1 - N)

theorem blkN_mul_neg (N : Matrix ι ι A) : blkN N * blkN (-N) = 1 := by
  rw [blkN, blkN, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> noncomm_ring

theorem neg_mul_blkN (N : Matrix ι ι A) : blkN (-N) * blkN N = 1 := by
  have h := blkN_mul_neg (-N)
  rwa [neg_neg] at h

theorem blkN_eq (N : Matrix ι ι A) :
    1 + (fromRows (1 : Matrix ι ι A) (-1) * N) * (fromRows (1 : Matrix ι ι A) 1)ᵀ = blkN N := by
  rw [fromRows_mul, transpose_fromRows, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_add, blkN]
  simp [sub_eq_add_neg]

-- Select matrix multiplication explicitly to avoid the `CStarMatrix` default instance.
local infixl:70 " ⬝ₘ " => @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem blkN_anti (N : Matrix ι ι A) : blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) (-1) = fromRows 1 (-1) := by
  rw [blkN, fromBlocks_mul_fromRows]
  congr 1 <;> noncomm_ring

theorem blkN_diag (N : Matrix ι ι A) :
    blkN N ⬝ₘ fromRows (1 : Matrix ι ι A) 1 = fromRows 1 1 + fromRows (1 : Matrix ι ι A) (-1) ⬝ₘ (N + N) := by
  rw [blkN, fromBlocks_mul_fromRows, fromRows_mul]
  ext (i | i) j <;> simp <;> ring

theorem blkN_unitary (s : A →+* A) (J N : Matrix ι ι A) (h : Nᵀ * J + J * N.map s = 0) :
    (blkN N)ᵀ * dbl J * (blkN N).map s = dbl J := by
  have h1 : (1 + N).map s = 1 + N.map s := by
    rw [Matrix.map_add _ (map_add s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h2 : (1 - N).map s = 1 - N.map s := by
    rw [Matrix.map_sub _ (map_sub s), Matrix.map_one _ (map_zero s) (map_one s)]
  have h3 : (-N).map s = - N.map s := by ext i j; simp
  rw [blkN, fromBlocks_map, fromBlocks_transpose, dbl, fromBlocks_multiply, fromBlocks_multiply, h1, h2, h3,
    transpose_add, transpose_sub, transpose_neg, transpose_one]
  generalize Nᵀ = P at h ⊢
  generalize N.map s = Q at h ⊢
  congr 1
  · calc _ = J + (P * J + J * Q) := by noncomm_ring
      _ = J := by rw [h, add_zero]
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = P * J + J * Q := by noncomm_ring
      _ = 0 := h
  · calc _ = -J + (P * J + J * Q) := by noncomm_ring
      _ = -J := by rw [h, add_zero]

theorem skew_block (s : A →+* A) (J K K' : Matrix ι ι A) (a c : A) (ha : s a = a) (hc : s c = -c)
    (hKK : K * K' = 1) (hKK' : K' * K = 1) (hK : Kᵀ * J * K.map s = J) (hK' : K'ᵀ * J * K'.map s = J) :
    (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1)))ᵀ * J +
      J * (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s = 0 := by
  have e1 : J * K.map s = K'ᵀ * J := by
    calc J * K.map s = (K * K')ᵀ * J * K.map s := by rw [hKK, transpose_one, Matrix.one_mul]
      _ = K'ᵀ * (Kᵀ * J * K.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK]
  have e2 : J * K'.map s = Kᵀ * J := by
    calc J * K'.map s = (K' * K)ᵀ * J * K'.map s := by rw [hKK', transpose_one, Matrix.one_mul]
      _ = Kᵀ * (K'ᵀ * J * K'.map s) := by rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK']
  have e3 : (a • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))).map s =
      a • ((1 + c) • (K.map s - 1) - (1 - c) • (K'.map s - 1)) := by
    ext i j
    have h1 : s ((1 : Matrix ι ι A) i j) = (1 : Matrix ι ι A) i j :=
      congrFun (congrFun (Matrix.map_one s (map_zero _) (map_one _)) i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul, map_sub, map_add (f := _), map_one,
      ha, hc, h1]
    ring
  rw [e3]
  simp only [transpose_smul, transpose_sub, transpose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, e1, e2]
  rw [← smul_add]
  simp

theorem blkN_mulVec_inl (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inl i)) =
      (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inl i)) + N *ᵥ (fun i => z (Sum.inr i)) := by
  rw [blkN, fromBlocks_mulVec, add_mulVec, one_mulVec]
  rfl

theorem blkN_mulVec_inr (N : Matrix ι ι A) (z : ι ⊕ ι → A) :
    (fun i => (blkN N *ᵥ z) (Sum.inr i)) =
      -(N *ᵥ (fun i => z (Sum.inl i))) + ((fun i => z (Sum.inr i)) - N *ᵥ (fun i => z (Sum.inr i))) := by
  rw [blkN, fromBlocks_mulVec, sub_mulVec, one_mulVec, neg_mulVec]
  rfl

theorem blkN_sub_one (N : Matrix ι ι A) : blkN N - 1 = fromBlocks N N (-N) (-N) := by
  ext (i | i) (j | j) <;> simp [blkN, Matrix.one_apply]

end Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem smul_mem_latAt_of_int {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) {x : AF F}
    (hx : evFin F v x ∈ v.adicCompletionIntegers F) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : x • y ∈ GlobalTheory.InertSph.latAt W v := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    rw [smul_smul]
    refine AddSubgroup.subset_closure ⟨x * a, ?_, ?_, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hx hv
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem evFin_invTwo_mem (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have h : evFin F v (⅟(2 : AF F)) * algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) = 1 := by
    rw [map_ofNat, map_ofNat, ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F 2)) = 1 := by
    have := v.valuedAdicCompletion_eq_valuation' (K := F) (algebraMap (𝓞 F) F 2)
    rw [HeightOneSpectrum.valuation_of_algebraMap, (HeightOneSpectrum.intValuation_eq_one_iff).2 h2] at this
    exact this
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h' := congrArg (Valued.v : v.adicCompletion F → _) h
  rw [map_mul, map_one, hv, mul_one] at h'
  exact h'.le

theorem half_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (GlobalTheory.SplitDblGen.half : AE F E) • y ∈ GlobalTheory.InertSph.latAt W v := by
  rw [GlobalTheory.SplitDblGen.half, algebraMap_smul]
  exact smul_mem_latAt_of_int W v (evFin_invTwo_mem v h2) hy

theorem nMat_mem_NabD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ n ∈ GlobalTheory.InertDbl.NabD σ W v,
      GlobalTheory.InertDbl.matD n = GlobalTheory.SplitDblGen.nMat c (mat k) (mat k⁻¹) := by
  intro F E _ _ _ _ _ σ d W v h2 c hc hcL k hk
  set N := GlobalTheory.SplitDblGen.splitDoublingNBlock c (mat k) (mat k⁻¹) with hN
  have hKK : mat k * mat k⁻¹ = 1 := congrArg Units.val (mul_inv_cancel (k : GL (Fin d) (AE F E)))
  have hKK' : mat k⁻¹ * mat k = 1 := congrArg Units.val (inv_mul_cancel (k : GL (Fin d) (AE F E)))
  have hhalf : (cA σ) (GlobalTheory.SplitDblGen.half : AE F E) = GlobalTheory.SplitDblGen.half := (cA σ).commutes _
  have hsk : Nᵀ * incM F W.J + incM F W.J * N.map (cA σ : AE F E →+* AE F E) = 0 :=
    skew_block (cA σ : AE F E →+* AE F E) (incM F W.J) (mat k) (mat k⁻¹) _ c
      (by simp only [RingHom.coe_coe, map_mul, hhalf]) hc hKK hKK' k.2 (k⁻¹).2
  have hNL : ∀ z ∈ GlobalTheory.InertSph.latAt W v, N *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro z hz
    have a1 : (mat k - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).1 hz
    have a2 : (mat k⁻¹ - 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
      rw [sub_mulVec, one_mulVec]; exact sub_mem (hk.2 z hz).2 hz
    rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_mulVec, mul_smul, mul_smul, sub_mulVec, smul_mulVec, smul_mulVec, sub_smul,
      add_smul, one_smul, one_smul]
    exact half_smul_mem W v h2 (half_smul_mem W v h2 (half_smul_mem W v h2
      (sub_mem (sub_mem a1 (hcL _ a1)) (add_mem a2 (hcL _ a2)))))
  have hblk : ∀ M : Matrix (Fin d) (Fin d) (AE F E), (∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z ∈ GlobalTheory.InertDbl.latAtD W v, blkN M *ᵥ z ∈ GlobalTheory.InertDbl.latAtD W v := by
    intro M hM z hz
    refine ⟨?_, ?_⟩
    · rw [blkN_mulVec_inl]; exact add_mem (add_mem hz.1 (hM _ hz.1)) (hM _ hz.2)
    · rw [blkN_mulVec_inr]; exact add_mem (neg_mem (hM _ hz.1)) (sub_mem hz.2 (hM _ hz.2))
  refine ⟨⟨⟨blkN N, blkN (-N), blkN_mul_neg N, neg_mul_blkN N⟩,
    blkN_unitary (cA σ : AE F E →+* AE F E) _ N hsk⟩, ⟨⟨fun u hu => ?_, fun z hz => ⟨hblk N hNL z hz, ?_⟩⟩,
      blkN_anti N, N + N, blkN_diag N⟩, (blkN_eq N).symm⟩
  · have b1 : u • (mat k - 1) = 0 := hk.1 u hu
    have b2 : u • (mat k⁻¹ - 1) = 0 := by
      have e1 : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by
        rw [Matrix.mul_sub, hKK', Matrix.mul_one, neg_sub]
      rw [e1, smul_neg, ← Matrix.mul_smul, b1, Matrix.mul_zero, neg_zero]
    have b3 : u • N = 0 := by
      rw [hN, GlobalTheory.SplitDblGen.splitDoublingNBlock, smul_comm u, smul_sub u, smul_comm u, smul_comm u (1 + c), b1, b2, smul_zero,
        smul_zero, sub_zero, smul_zero]
    show u • (blkN N - 1) = 0
    rw [blkN_sub_one, fromBlocks_smul, smul_neg, b3, neg_zero, fromBlocks_zero]
  · exact hblk (-N) (fun y hy => by rw [neg_mulVec]; exact neg_mem (hNL y hy)) z hz

end GlobalTheory.SplitDblNab
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblIdent

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open Matrix in
theorem fromRows_add_fromRows {R : Type} [Add R] {m₁ m₂ n : Type} (A B : Matrix m₁ n R) (C D : Matrix m₂ n R) :
    fromRows A C + fromRows B D = fromRows (A + B) (C + D) := by
  ext (i | i) j <;> rfl

open Matrix in
theorem smul_fromRows {R S : Type} [SMul S R] {m₁ m₂ n : Type} (s : S) (A : Matrix m₁ n R) (C : Matrix m₂ n R) :
    s • fromRows A C = fromRows (s • A) (s • C) := by
  ext (i | i) j <;> rfl

theorem nT_eq {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (X Y : Matrix (Fin d) (Fin d) R)
    (h2 : (Y + 1) * (X + 1) = 1) (hc : (c * c) • X = X) :
    ((h * h * h) • ((1 - c) • X - (1 + c) • Y)) * (1 + (h * (1 + c)) • X) = (h * h) • X := by
  have hYX : Y * X = -X - Y := by
    have e : Y * X + X + Y = 0 := by
      have := h2; rw [add_mul, mul_add, mul_add, mul_one, one_mul, one_mul] at this
      rw [← sub_eq_zero] at this; rw [← this]; abel
    rw [← sub_eq_zero, ← e]; abel
  have hY : (c * c) • Y = Y := by
    have e : Y = -((Y + 1) * X) := by
      rw [add_mul, one_mul, hYX]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hc]
  have hXX : (c * c) • (X * X) = X * X := by rw [← Matrix.smul_mul, hc]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_mul, Matrix.add_mul,
    smul_sub, smul_add, smul_smul, Matrix.mul_sub]
  linear_combination (norm := module) (-(h ^ 4 * (1 + c) ^ 2)) • hYX - h ^ 4 • hXX + h ^ 4 • hc + h ^ 4 • hY +
    hh • ((h ^ 3 * (1 + c) + h ^ 2) • X + (h ^ 3 * (1 + c)) • Y)

theorem blocks {R : Type} [CommRing R] {d : ℕ} (h c : R) (hh : h * 2 = 1) (K N T : Matrix (Fin d) (Fin d) R)
    (hT : T = 1 + (h * (1 + c)) • (K - 1)) (hNT : N * T = (h * h) • (K - 1)) :
    (1 + (h * c) • (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R))ᵀ)) *
        Matrix.fromBlocks K 0 0 (1 : Matrix (Fin d) (Fin d) R) * Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) =
      (1 + Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (-1 : Matrix (Fin d) (Fin d) R) * N * (Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R))ᵀ) *
        Matrix.fromRows (1 : Matrix (Fin d) (Fin d) R) (1 : Matrix (Fin d) (Fin d) R) * T := by
  simp only [Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg, Matrix.add_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.fromRows_mul,
    Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_add, smul_fromRows,
    fromRows_add_fromRows, hNT]
  rw [Matrix.fromRows_inj.eq_iff]
  subst hT
  constructor
  · linear_combination (norm := module) hh • (-(h + 1) • (K - 1))
  · linear_combination (norm := module) hh • (h • (K - 1))

end GlobalTheory.SplitDblIdent

namespace GlobalTheory.SplitDblGen

theorem half_mul_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    (half : AE F E) * 2 = 1 := by
  rw [half, show (2 : AE F E) = algebraMap (AF F) (AE F E) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem diagonalFixingDoubling_mul_firstFactor_lagrangian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : AE F E) (K K' : Matrix (Fin d) (Fin d) (AE F E)),
    K * K' = 1 → K' * K = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d * Matrix.fromBlocks K 0 0 1 * diagCols (E := AE F E) (Fin d) =
      GlobalTheory.SplitDblGen.nMat c K K' * diagCols (E := AE F E) (Fin d) * GlobalTheory.SplitDblGen.tMat c K := by
  intro F E _ _ _ _ _ d c K K' _ h2 hc
  have hNT := GlobalTheory.SplitDblIdent.nT_eq half c half_mul_two (K - 1) (K' - 1) (by simpa using h2) hc
  exact GlobalTheory.SplitDblIdent.blocks half c half_mul_two K (splitDoublingNBlock c K K') (tMat c K) rfl hNT

end GlobalTheory.SplitDblGen
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

theorem continuous_archAct_line : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W), ∀ γ ∈ Lines σ W,
    ∀ v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archAct M (γ (Multiplicative.ofAdd t)) v := by
  intro F E _ _ _ _ _ σ n d X W M γ hγ v
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have hγc : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.1.comp continuous_ofAdd
  have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
    ((Units.continuous_val.comp continuous_subtype_val).comp hγc).matrix_transpose
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hev : Continuous (evI F) := by
    change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
    refine Continuous.comp ?_ continuous_fst
    change Continuous fun x : InfiniteAdeleRing F =>
      ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
    refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
  have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
  show Continuous fun t : ℝ =>
    (locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
     locV (M.co.e (mat (1 : UA σ X.J) * M.co.e.symm (liftV v.1, liftV v.2) * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
  exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp
    (he.comp (continuous_const.matrix_mul hm))

end GlobalTheory.ArchLine
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∃ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 ∧ (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) ∧ (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) ∧ (∀ ℓ' : M →ₗ[ℂ] ℂ, (∀ a ∈ mixLat L n' n, ∀ v, ℓ' (ρ a v) = ℓ' v) → ∀ v, ℓ' v = ℓ' s * ℓ v) ∧ ∀ (z : Matrix (Fin (n' / 2)) (Fin (n / 2)) L), ℓ (ρ (embLow n' n z) s) = if z ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) then 1 else 0 := by
  first | exact @GlobalTheory.SphTheta.exists_mixLat_form | exact GlobalTheory.SphTheta.exists_mixLat_form | (intros; apply GlobalTheory.SphTheta.exists_mixLat_form <;> assumption)
end
