module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle003
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def compHom {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) :
    AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ := (θ τ).comp (infPart D)

theorem adele_ext {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {a b : AF D.host.F ⊗[D.host.F] D.host.E} (hf : finPart D a = finPart D b)
    (hc : ∀ τ, compHom θ τ a = compHom θ τ b) : a = b := by
  obtain ⟨w, -, hw⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ 1 1 hθ (fun _ _ _ => 0)
  have h0 : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 := by
    intro c h1 h2
    have e1 : (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) _) = w := hw _ ⟨by
      ext i j
      exact h1, fun τ => by
      ext i j
      exact h2 τ⟩
    have e2 : (0 : Matrix (Fin 1) (Fin 1) (AF D.host.F ⊗[D.host.F] D.host.E)) = w := hw _ ⟨by
      ext i j
      exact map_zero (finPart D), fun τ => by
      ext i j
      exact map_zero (compHom θ τ)⟩
    exact congrFun (congrFun (e1.trans e2.symm) 0) 0
  refine sub_eq_zero.1 (h0 _ ?_ fun τ => ?_)
  · rw [map_sub, hf, sub_self]
  · rw [map_sub, hc, sub_self]

theorem compHom_adMat {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (Y : Matrix (Fin a) (Fin b) D.host.E) :
    (adMat D.host.F Y).map (compHom θ τ) = Y.map (tauE D τ) := by
  ext i j
  have : infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] Y i j := by
    simp [infPart]
  simp only [Matrix.map_apply, adMat, compHom, RingHom.comp_apply]
  show θ τ (infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j)) = _
  rw [this]
  exact (hθ τ).1 _

theorem map_one_add_of {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    {p : Matrix (Fin n) (Fin a) B} {q : Matrix (Fin a) (Fin n) B} {r : Matrix (Fin n) (Fin b) B} {s : Matrix (Fin b) (Fin n) B}
    (hp : P.map φ = p) (hq : Q.map φ = q) (hr : R.map φ = r) (hs : S.map φ = s) :
    (1 + P * Q + R * S).map φ = 1 + p * q + r * s := by
  subst hp hq hr hs
  rw [Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.map_mul]

theorem map_one_add_of_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    (hq : Q.map φ = 0) (hr : R.map φ = 0) : (1 + P * Q + R * S).map φ = 1 := by
  rw [map_one_add_of φ P Q R S rfl hq hr rfl, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

theorem matrix_ext_parts {D : D7} {n : ℕ} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    (M N : Matrix (Fin n) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hf : M.map (finPart D) = N.map (finPart D)) (hc : ∀ τ, M.map (compHom θ τ) = N.map (compHom θ τ)) : M = N := by
  ext i j
  exact adele_ext hθ (congrFun (congrFun hf i) j) fun τ => congrFun (congrFun (hc τ) i) j

theorem map_compHom_mul {D : D7} {a b c : ℕ} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau)
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (compHom θ τ) = A.map (compHom θ τ) * B.map (compHom θ τ) := Matrix.map_mul

theorem map_finPart_mul {D : D7} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) := Matrix.map_mul

theorem compHom_adMat_adj {D : D7} {m : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (V : HSp D) (X : Matrix (Fin V.rank) (Fin m) D.host.E) :
    (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (compHom θ τ) =
      (X.map (tauE D τ))ᴴ * gramAt D V τ := by
  rw [compHom_adMat τ θ hθ, Matrix.map_mul]
  congr 1
  ext i j
  exact GlobalTheory.Mem.Isom.tauE_sig D τ (X j i)

theorem exists_adelic_of_real_comps : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D θ hθ V m X u w hU
  obtain ⟨-, h2⟩ := GlobalTheory.SmoothForms.RealPts.glue θ hθ V
  obtain ⟨g, hg, hgτ⟩ := h2 _ hU
  obtain ⟨U, ⟨hUf, hUc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ m V.rank hθ (fun τ i j => u τ i j)
  obtain ⟨W, ⟨hWf, hWc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ V.rank m hθ (fun τ i j => w τ i j)
  have hUc' : ∀ τ, U.map (compHom θ τ) = u τ := hUc
  have hWc' : ∀ τ, W.map (compHom θ τ) = w τ := hWc
  have hUf' : U.map (finPart D) = 0 := hUf
  have hWf' : W.map (finPart D) = 0 := hWf
  have hzero : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 :=
    fun c h1 h2 => adele_ext hθ (by rw [h1, map_zero]) fun τ => by rw [h2, map_zero]
  refine ⟨g, hgτ, U, W, fun i v h => ?_, fun v i h => ?_, fun i j h => ?_, ?_⟩
  · refine hzero _ (congrFun (congrFun hUf' i) v) fun τ => ?_
    rw [← h τ, ← hUc' τ]
    rfl
  · refine hzero _ (congrFun (congrFun hWf' v) i) fun τ => ?_
    rw [← h τ, ← hWc' τ]
    rfl
  · refine hzero _ ?_ fun τ => ?_
    · have e := map_finPart_mul U (adMat D.host.F X)
      rw [hUf', Matrix.zero_mul] at e
      exact congrFun (congrFun e i) j
    · have e := map_compHom_mul θ τ U (adMat D.host.F X)
      rw [hUc', compHom_adMat τ θ hθ] at e
      rw [← h τ, ← e]
      rfl
  · have hf : (matHom V g).1.map (finPart D) = 1 := by
      have hg' : finHom V g = 1 := hg
      have e : (finHom V g).1 = (matHom V g).1.map (finPart D) := rfl
      rw [← e, hg', Units.val_one]
    refine matrix_ext_parts hθ _ _ ?_ fun τ => ?_
    · exact hf.trans (map_one_add_of_zero (finPart D) _ _ _ _ hUf' hWf').symm
    · have e := map_one_add_of (compHom θ τ) (adMat D.host.F X) U W
        (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram))
        (compHom_adMat τ θ hθ X) (hUc' τ) (hWc' τ) (compHom_adMat_adj τ θ hθ V X)
      refine (hgτ τ).trans (Eq.trans ?_ e.symm)
      rw [Matrix.mul_assoc (w τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.IsoFrameBound

open Formalism.UG (cT)

variable {E : Type} [Field E]

theorem rank_map_of_invol (s : E →+* E) (hs : ∀ x, s (s x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    (A.map s).rank = A.rank := by
  have hAA : (A.map s).map s = A := by ext i j; simp [hs]
  have key : ∀ (B : Matrix (Fin a) (Fin b) E) (v : Fin a → E), v ∈ LinearMap.range B.mulVecLin →
      (fun i => s (v i)) ∈ LinearMap.range (B.map s).mulVecLin := by
    rintro B v ⟨w, rfl⟩
    refine ⟨fun i => s (w i), ?_⟩
    funext i
    simp only [Matrix.mulVecLin_apply]
    exact (RingHom.map_mulVec s B w i).symm
  let j : LinearMap.range A.mulVecLin ≃+ LinearMap.range (A.map s).mulVecLin :=
    { toFun := fun v => ⟨fun i => s (v.1 i), key A v.1 v.2⟩
      invFun := fun v => ⟨fun i => s (v.1 i), by
        have := key (A.map s) v.1 v.2
        rwa [hAA] at this⟩
      left_inv := fun v => by ext i; simp [hs]
      right_inv := fun v => by ext i; simp [hs]
      map_add' := fun v w => by ext i; simp }
  have hb : Function.Bijective s := ⟨s.injective, fun x => ⟨s x, hs x⟩⟩
  have := rank_eq_of_equiv_equiv s j hb (fun c v => Subtype.ext (funext fun i => by
    show s (c * v.1 i) = s c * s (v.1 i)
    exact map_mul s _ _))
  rw [← Matrix.finrank_range_mulVecLin, ← Matrix.finrank_range_mulVecLin]
  exact congrArg Cardinal.toNat this.symm

theorem hform_eq (s : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dot_cT (s : E →+* E) {n k : ℕ} (P : Matrix (Fin n) (Fin k) E) (J : Matrix (Fin n) (Fin n) E)
    (u : Fin k → E) (v : Fin n → E) :
    (fun i => s ((P *ᵥ u) i)) ⬝ᵥ (J *ᵥ v) = (fun i => s (u i)) ⬝ᵥ ((cT s P * J) *ᵥ v) := by
  have e : (fun i => s (u i)) ᵥ* cT s P = fun i => s ((P *ᵥ u) i) := by
    show _ ᵥ* (P.map s)ᵀ = _
    rw [Matrix.vecMul_transpose]
    funext i
    exact (RingHom.map_mulVec s P u i).symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (fun i => s (u i)) (cT s P) (J *ᵥ v), e]

theorem le_of_frames (s : E →+* E) (hs : ∀ x, s (s x) = x) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : cT s J = J) (X Y : Matrix (Fin n) (Fin m) E) (C : Matrix (Fin n) (Fin r) E)
    (xx : cT s X * J * X = 0) (yx : cT s Y * J * X = 1) (cc : cT s C * J * C = 0)
    (an : ∀ z : Fin n → E, (cT s X * J) *ᵥ z = 0 → (cT s Y * J) *ᵥ z = 0 → Formalism.UG.hform s J z z = 0 → z = 0)
    (hC : LinearIndependent E Cᵀ) : r ≤ m := by
  obtain ⟨M, hM⟩ : ∃ M, M = cT s X * J * C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cT s Y * J * C := ⟨_, rfl⟩
  obtain ⟨M', hM'⟩ : ∃ M', M' = cT s C * J * X := ⟨_, rfl⟩
  have hXX : cT s (cT s X) = X := by ext i j; simp [cT, hs]
  have hMM : M' = cT s M := by
    rw [hM, hM', Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ, hXX, Matrix.mul_assoc]
  have step : ∀ a, M *ᵥ a = 0 → X *ᵥ (Q *ᵥ a) = C *ᵥ a := by
    intro a ha
    obtain ⟨b, hb⟩ : ∃ b, b = Q *ᵥ a := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, z = C *ᵥ a - X *ᵥ b := ⟨_, rfl⟩
    have hA : (cT s X * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ha, xx,
        Matrix.zero_mulVec, sub_zero]
    have hB : (cT s Y * J) *ᵥ z = 0 := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, yx, Matrix.one_mulVec, ← hQ, hb,
        sub_self]
    have hh : Formalism.UG.hform s J z z = 0 := by
      rw [hform_eq]
      have e1 : (fun i => s (z i)) = (fun i => s ((C *ᵥ a) i)) - (fun i => s ((X *ᵥ b) i)) := by
        funext i; simp [hz]
      have e2 : (cT s C * J) *ᵥ z = - (M' *ᵥ b) := by
        rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec, zero_sub, hM']
      have e3 : (fun i => s (a i)) ᵥ* cT s M = 0 := by
        show _ ᵥ* (M.map s)ᵀ = 0
        rw [Matrix.vecMul_transpose]
        funext i
        have := RingHom.map_mulVec s M a i
        rw [ha] at this
        exact this.symm.trans (by simp)
      rw [e1, sub_dotProduct, dot_cT, dot_cT, hA, dotProduct_zero, sub_zero, e2, dotProduct_neg, neg_eq_zero,
        hMM, Matrix.dotProduct_mulVec, e3, zero_dotProduct]
    have h0 := an z hA hB hh
    rw [← hb]
    rw [hz] at h0
    exact (sub_eq_zero.1 h0).symm
  have hCi : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  let φ : LinearMap.ker M.mulVecLin →ₗ[E] LinearMap.ker M'.mulVecLin :=
    (Q.mulVecLin.comp (LinearMap.ker M.mulVecLin).subtype).codRestrict _ (fun a => by
      have ha : M *ᵥ a.1 = 0 := a.2
      rw [LinearMap.mem_ker]
      show M' *ᵥ (Q *ᵥ a.1) = 0
      rw [hM', ← Matrix.mulVec_mulVec, step a.1 ha, Matrix.mulVec_mulVec, cc, Matrix.zero_mulVec])
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a h => ?_
    have h1 : Q *ᵥ a.1 = 0 := congrArg Subtype.val h
    have ha : M *ᵥ a.1 = 0 := a.2
    have h2 := step a.1 ha
    rw [h1, Matrix.mulVec_zero] at h2
    exact Subtype.ext (hCi (h2.symm.trans (Matrix.mulVec_zero C).symm))
  have h1 := LinearMap.finrank_le_finrank_of_injective hφ
  have h2 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker M'.mulVecLin
  have h4 : M'.rank = M.rank := by
    rw [hMM]
    simp only [cT]
    rw [Matrix.rank_transpose, rank_map_of_invol s hs]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2 h3
  have h5 : Module.finrank E (LinearMap.range M.mulVecLin) = M.rank := by rw [Matrix.finrank_range_mulVecLin]
  have h6 : Module.finrank E (LinearMap.range M'.mulVecLin) = M'.rank := by rw [Matrix.finrank_range_mulVecLin]
  omega

theorem isoFrame_le_wittFrame : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E),
    IsIsoFrame V C → r ≤ m := by
  intro D V m X Y hW r C hC
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  exact le_of_frames (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => by simp only [hσ, star_star]) V.gram hJ X Y C
    hW.xx (GlobalTheory.WittFrame.yx_eq_one D V m X Y hW) hC.2.2 (fun z h1 h2 h3 => hW.aniso z h1 h2 h3) hC.2.1

end GlobalTheory.CompanionTheory.IsoFrameBound
end
end
