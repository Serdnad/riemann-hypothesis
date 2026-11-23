module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle279
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.FirstClauseRankZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle030
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelCone

theorem cone_integral_zero_vars_lt_top :
    ∀ (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ),
      ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n d c
  have h : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := by
    intro t
    simp [GlobalTheory.SiegelSet.modulus]
  simp_rw [h]
  rw [setLIntegral_const, one_mul]
  exact measure_lt_top _ _

end GlobalTheory.CompanionTheory.SiegelCone
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WittFrame

open Matrix

theorem length_le_wittIdx (D : D7) (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf) : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  have hc : ∀ {a : ℕ} (A : Matrix (Fin V.rank) (Fin a) D.host.E),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
    intro a A
    exact Matrix.ext fun i j => rfl
  have hxx : Xfᴴ * V.gram * Xf = 0 := by rw [← hc]; exact hW.xx
  have hxy : Xfᴴ * V.gram * Yf = 1 := by rw [← hc]; exact hW.xy
  have hG : V.gramᴴ = V.gram := by
    refine Matrix.ext fun a b => ?_
    exact V.herm.eq _ _
  have hyx : Yfᴴ * V.gram * Xf = 1 := by
    have h := congrArg conjTranspose hxy
    simpa [conjTranspose_mul, hG, Matrix.mul_assoc] using h
  let f : (Fin r → D.host.E) →ₗ[D.host.E] V.V := V.frame.equivFun.symm.toLinearMap.comp Xf.mulVecLin
  have hf : Function.Injective f := by
    refine V.frame.equivFun.symm.injective.comp (g := V.frame.equivFun.symm) (f := Xf.mulVec) fun v w hvw => ?_
    have := congrArg (Yfᴴ * V.gram).mulVec hvw
    simpa [mulVec_mulVec, hyx] using this
  refine le_csSup (GlobalTheory.SiegelFormula.Model.bddAbove_witt V) ⟨LinearMap.range f, by simpa using LinearMap.finrank_range_of_inj hf, ?_⟩
  rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
  change V.hT (V.frame.equivFun.symm (Xf *ᵥ v)) (V.frame.equivFun.symm (Xf *ᵥ w)) = 0
  rw [GlobalTheory.ParallelWitt.form_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hxx]
  simp

end GlobalTheory.CompanionTheory.WittFrame
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem exists_coords {K : Type} [Field K] {n : ℕ} (S : Submodule K (Fin n → K)) (P : Matrix (Fin n) (Fin n) K)
    (hP : ∀ v, P *ᵥ v ∈ S) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K),
      (∀ w, Z *ᵥ w ∈ S) ∧ Z * C = P ∧ Function.Injective Z.mulVec := by
  classical
  let b := Module.finBasis K S
  let Z : Matrix (Fin n) (Fin (Module.finrank K S)) K := Matrix.of fun i k => (b k : Fin n → K) i
  have hZ : ∀ w, Z *ᵥ w = ((∑ k, w k • b k : S) : Fin n → K) := by
    intro w
    ext i
    simp [Z, Matrix.mulVec, dotProduct, mul_comm, Submodule.coe_sum, Finset.sum_apply]
  let L : (Fin n → K) →ₗ[K] S := P.mulVecLin.codRestrict S hP
  let c : (Fin n → K) →ₗ[K] (Fin (Module.finrank K S) → K) := b.equivFun.toLinearMap ∘ₗ L
  refine ⟨_, Z, LinearMap.toMatrix' c, fun w => by rw [hZ]; exact Subtype.property _, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec, hZ]
    have : (∑ k, c v k • b k : S) = L v := b.sum_equivFun (L v)
    rw [this]
    rfl
  · intro w w' h
    rw [hZ, hZ] at h
    have h' := Subtype.coe_injective h
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h'
    exact b.equivFun.symm.injective h'

theorem exists_witt_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (Qi : Matrix (Idx r m) (Fin n) E), cT (σ : E →+* E) X * J * Z = 0 ∧ cT (σ : E →+* E) Y * J * Z = 0 ∧ Qi * frm X Z Y = 1 ∧ frm X Z Y * Qi = 1 := by
  intro F E _ _ _ _ _ σ hσ n J hJ r X Y hW
  have hc : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := Matrix.ext fun i j => sigma_sigma hσ _
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := hA ▸ hW.xx
  have hBY : B * Y = 0 := hB ▸ hW.yy
  have hAY : A * Y = 1 := hA ▸ hW.xy
  have hBX : B * X = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hc, hcc, Formalism.UG.cT_one, ← Matrix.mul_assoc] at h
    rw [hB, h]
  obtain ⟨P, hPd⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAP : A * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hBP : B * P = 0 := by
    rw [hPd, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX, hBY,
      Matrix.zero_mul, Matrix.one_mul, sub_zero, sub_self]
  have hPX : P * X = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBX, hAX,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  have hPY : P * Y = 0 := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBY, hAY,
      Matrix.mul_one, Matrix.mul_zero, sub_zero, sub_self]
  obtain ⟨m, Z, C, hS, hZC, hinj⟩ := exists_coords
    (LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) P (fun v => by
      refine ⟨?_, ?_⟩
      · simp [Matrix.mulVec_mulVec, hAP]
      · simp [Matrix.mulVec_mulVec, hBP])
  have hAZ : A * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).1
  have hBZ : B * Z = 0 := by
    apply Matrix.mulVec_injective
    funext w
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    simpa using (hS w).2
  have hcan : ∀ {ι : Type} (M M' : Matrix (Fin m) ι E), Z * M = Z * M' → M = M' := by
    intro ι M M' h
    ext i j
    exact congrFun (hinj (a₁ := fun i => M i j) (a₂ := fun i => M' i j)
      (funext fun a => congrFun (congrFun h a) j)) i
  have hPZ : P * Z = Z := by
    rw [hPd, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hBZ, hAZ,
      Matrix.mul_zero, Matrix.mul_zero, sub_zero, sub_zero]
  have hCZ : C * Z = 1 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPZ, Matrix.mul_one])
  have hCX : C * X = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPX, Matrix.mul_zero])
  have hCY : C * Y = 0 := hcan _ _ (by rw [← Matrix.mul_assoc, hZC, hPY, Matrix.mul_zero])
  refine ⟨m, Z, Matrix.fromRows B (Matrix.fromRows C A), hA ▸ hAZ, hB ▸ hBZ, ?_, ?_⟩
  · rw [frm, Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      hBX, hBZ, hBY, hCX, hAX, hCZ, hCY, hAZ, hAY]
    ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply]
  · rw [frm, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, hZC, hPd]
    abel

end GlobalTheory.CompanionTheory.CFin

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem torus_diag_witt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ n r m J X Y Z hXZ hYZ t a ha w τ
  obtain ⟨hX, hY, hZ⟩ := ha.2 w τ
  have hZc : archMat σ J τ (projArch σ J w a) * Z.map τ.1 = Z.map τ.1 := Matrix.ext fun i j => by
    have h := congrFun (hZ (fun l => Z l j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hXZ i) j)
      (funext fun i => by simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hYZ i) j)) i
    simpa [Matrix.mul_apply, mulVec, dotProduct] using h
  have e : (frm X Z Y).map τ.1 = Matrix.fromCols (X.map τ.1) (Matrix.fromCols (Z.map τ.1) (Y.map τ.1)) := by
    ext i (k | k | k) <;> rfl
  rw [e, Matrix.mul_fromCols, Matrix.mul_fromCols, hX, hY, hZc]
  ext i (k | k | k)
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]
  · simp [Matrix.mul_diagonal, wt]

end GlobalTheory.CompanionTheory.CFin

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.CFin

theorem stabUpTo_archMat_of_mem_minParOne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n r : ℕ) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) (p : GAd σ J), p ∈ minParOne σ J X → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (j : Fin r), StabUpTo (X.map τ.1) (archMat σ J τ (projArch σ J w p)) j := by
  intro F E _ _ _ _ _ σ h n r J X p hp w τ j
  have := h.1
  obtain ⟨B, hB, hE, -⟩ := hp
  let φ := (infEmb τ).comp (compInf F E w)
  have h0 : ∀ x : E, φ (inclR (F := F) (AF F) x) = τ.1 x := fun x => by
    change infEmb τ (evInf F w 1 ⊗ₜ[F] x) = _
    simp
  have h2 : (adMat F X).map φ = X.map τ.1 := Matrix.ext fun i j => h0 _
  have h3 : archMat σ J τ (projArch σ J w p) = (matHom _ σ J p).1.map φ := rfl
  have key : archMat σ J τ (projArch σ J w p) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [h3, ← h2, ← Matrix.map_mul, hE, Matrix.map_mul]
  intro l hl
  refine ⟨fun m => φ (B m l), ?_, fun m hm => ?_⟩
  · funext a
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply] using congrFun (congrFun key a) l
  · have e : B m l = 0 := hB (show id l < id m from lt_of_le_of_lt hl hm)
    change φ (B m l) = 0
    rw [e, map_zero]

end GlobalTheory.CompanionTheory.CFin

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_mul_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x y : E) :
    Algebra.trace F E (σ x * y) = Algebra.trace F E (x * σ y) := by
  have hinv : Function.Involutive σ := GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol h
  have key := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hinv.bijective) (σ x * y)
  rw [← key]
  simp [hinv x]

theorem trace_sigR_mul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u w : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * w) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr u k *
        ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * (Algebra.TensorProduct.basis R b).repr w l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have hC' : ∀ (r : R) (k : Fin d), r • C k = r ⊗ₜ[F] b k := by
    intro r k
    simp [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  conv_lhs => rw [← C.sum_repr u, ← C.sum_repr w]

  simp only [hC', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : sigR R σ (C.repr u k ⊗ₜ[F] b k) = C.repr u k ⊗ₜ[F] σ (b k) := by simp [sigR]
  rw [hs, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.GaussMean.OneVec.trace_tmul, trace_mul_sig h]
  ring

theorem mulVec_inl (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (i : Fin n) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inl i) = v (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, coordForm, Matrix.one_apply]

theorem mulVec_inr (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (k : Fin d)
    (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inr (k, q)) =
      ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * v (Sum.inr (l, q)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, coordForm, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.blockDiagonal_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    simp [hx, Ne.symm hx]
  · simp

theorem pairHerm_eq_coordForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n),
    pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  intro F E _ _ _ _ _ σ h R _ _ d b n S T
  rw [GlobalTheory.HermCoordEquiv.pair_eq R h S T]
  unfold GlobalTheory.HermSD.coordPair
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_inl, Fintype.sum_prod_type, mulVec_inr]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_sigR_mul h]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem trace_sigR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    (z : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ z) = Algebra.trace R (R ⊗[F] E) z := by
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  let e : (R ⊗[F] E) ≃ₐ[R] (R ⊗[F] E) := Algebra.TensorProduct.congr AlgEquiv.refl s
  have h : sigR R σ z = e z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [sigR, e, s]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h]
  exact Algebra.trace_eq_of_algEquiv e z

theorem hR_add_left (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_add_right (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Gen

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem trace_gram2_swap (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J Y X)) =
      Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)) := by
  rw [← trace_sigR (Af F) σ hσ]
  congr 1

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, gram2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  have hb : sigR (Af F) σ ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) c a) = (b : Matrix _ _ _) a c := b.2 a c
  rw [hb, GlobalTheory.CompanionTheory.SiegelND.Coef.sigR_hR (Af F) σ hσ hJ]

theorem gramR_add (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    gramR (Af F) σ J (X + Y) = gramR (Af F) σ J X + gramR (Af F) σ J Y + gram2 σ J X Y + gram2 σ J Y X := by
  funext a c
  simp only [gramR, gram2, Pi.add_apply, Matrix.add_apply, hR_add_left, hR_add_right]
  abel

end Fin

theorem psiFin_add {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (u v : Af F) :
    psiFin F ψ (u + v) = psiFin F ψ u * psiFin F ψ v := by
  have h : pairA F 0 (u + v) = pairA F 0 u + pairA F 0 v := by
    have h0 : (0 : Ainf F) = 0 + 0 := (add_zero 0).symm
    exact congrArg (fun t => pairA F t (u + v)) h0
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem phaseB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n)
    (X Y : Fin n → Fin M → Af F ⊗[F] E),
    phaseB σ J (psiFin F ψ) b (X + Y) =
      phaseB σ J (psiFin F ψ) b X * phaseB σ J (psiFin F ψ) b Y * pairB σ J (psiFin F ψ) b X Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ n ψ _ b X Y
  have hsw := trace_gram2_swap σ (GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol hCM) hJ.1 b X Y
  have h2 : algebraMap F (Af F) (1 / 2) + algebraMap F (Af F) (1 / 2) = 1 := by
    rw [← map_add (f := _)]
    norm_num
  simp only [phaseB, pairB]
  rw [← psiFin_add, ← psiFin_add]
  congr 1
  rw [gramR_add, mul_add, mul_add, mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    map_add, map_add, map_add, hsw]
  linear_combination (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y))) * h2

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PhaseAdd
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.archimedean_volume_rank_one_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) (m : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) = ENNReal.ofReal (D (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density | exact GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Inf0.fibre_rapid_zero_eq_density <;> assumption)
end
