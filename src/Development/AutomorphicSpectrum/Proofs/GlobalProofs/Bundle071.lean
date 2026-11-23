module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchMatBlockEmbInfGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConjugatedMatrixUnitEntries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle069
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemFormsOnOfMemSpan

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis

theorem exists_basis_of_duality {E : Type} [Field E] {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) E)
    (A B : Matrix (Fin m) (Fin n) E) (hAX : A * X = 1) (hAY : A * Y = 0) (hBX : B * X = 0) (hBY : B * Y = 1) :
    2 * m ≤ n ∧ ∃ C : GL (Fin n) E,
      (∀ (i : Fin n) (j : Fin m), i.val = j.val → ∀ k, C.1 k i = X k j) ∧
      (∀ (i : Fin n) (j : Fin m), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j) ∧
      (∀ i : Fin n, m ≤ i.val → i.val + m < n →
        A *ᵥ (fun k => C.1 k i) = 0 ∧ B *ᵥ (fun k => C.1 k i) = 0) := by
  classical
  set P : Matrix (Fin m ⊕ Fin m) (Fin n) E := Matrix.fromRows A B with hP
  have hPQ : P * Matrix.fromCols X Y = 1 := by
    rw [hP, Matrix.fromRows_mul_fromCols, hAX, hAY, hBX, hBY, Matrix.fromBlocks_one]
  have hsurj : Function.Surjective P.mulVecLin := fun u => ⟨Matrix.fromCols X Y *ᵥ u, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]⟩
  have hrk := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at hrk
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hrk
  have hmem : ∀ k, k ∈ LinearMap.ker P.mulVecLin ↔ A *ᵥ k = 0 ∧ B *ᵥ k = 0 := by
    intro k
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hP, Matrix.fromRows_mulVec]
    constructor
    · intro h
      exact ⟨funext fun i => congrFun h (Sum.inl i), funext fun i => congrFun h (Sum.inr i)⟩
    · rintro ⟨h1, h2⟩
      funext i
      cases i <;> simp [h1, h2]
  set K := LinearMap.ker P.mulVecLin with hK
  let b := Module.finBasis E K
  have hle : 2 * m ≤ n := by omega
  refine ⟨hle, ?_⟩
  let col : Fin n → Fin n → E := fun i =>
    if h1 : i.val < m then fun k => X k ⟨i.val, h1⟩
    else if h2 : i.val + m < n then (b ⟨i.val - m, by have := i.2; omega⟩ : K).1
    else fun k => Y k ⟨n - 1 - i.val, by have := i.2; omega⟩
  let C0 : Matrix (Fin n) (Fin n) E := Matrix.of fun k i => col i k
  have hcol : ∀ i, col i ∈ LinearMap.range C0.mulVecLin := fun i =>
    ⟨Pi.single i 1, by
      funext k
      simp [Matrix.mulVecLin_apply, C0]⟩
  have hX : ∀ (j : Fin m), (fun k => X k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hi : j.val < n := by have := j.2; omega
    have := hcol ⟨j.val, hi⟩
    simpa [col] using this
  have hY : ∀ (j : Fin m), (fun k => Y k j) ∈ LinearMap.range C0.mulVecLin := by
    intro j
    have hj := j.2
    have hi : n - 1 - j.val < n := by omega
    have := hcol ⟨n - 1 - j.val, hi⟩
    have e1 : ¬ (n - 1 - j.val < m) := by omega
    have e2 : ¬ (n - 1 - j.val + m < n) := by omega
    have e3 : n - 1 - (n - 1 - j.val) = j.val := by omega
    simpa [col, e1, e2, e3] using this
  have hb : ∀ (t : Fin (Module.finrank E K)), (b t : K).1 ∈ LinearMap.range C0.mulVecLin := by
    intro t
    have ht := t.2
    have hi : t.val + m < n := by omega
    have := hcol ⟨t.val + m, hi⟩
    have e1 : ¬ (t.val + m < m) := by omega
    have e2 : t.val + m + m < n := by omega
    simpa [col, e1, e2] using this
  have hKr : ∀ k : K, k.1 ∈ LinearMap.range C0.mulVecLin := by
    intro k
    rw [← b.sum_repr k]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hb t)
  have hmv : ∀ (Z : Matrix (Fin n) (Fin m) E), (∀ j : Fin m, (fun k => Z k j) ∈ LinearMap.range C0.mulVecLin) →
      ∀ u, Z *ᵥ u ∈ LinearMap.range C0.mulVecLin := by
    intro Z hZ u
    have : Z *ᵥ u = ∑ j, u j • (fun k => Z k j) := by
      funext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hZ t)
  have hs : Function.Surjective C0.mulVec := by
    intro v
    have hk : v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v) ∈ K := by
      have eAX : ∀ w, A *ᵥ (X *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hAX, Matrix.one_mulVec]
      have eAY : ∀ w, A *ᵥ (Y *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hAY, Matrix.zero_mulVec]
      have eBX : ∀ w, B *ᵥ (X *ᵥ w) = 0 := fun w => by rw [Matrix.mulVec_mulVec, hBX, Matrix.zero_mulVec]
      have eBY : ∀ w, B *ᵥ (Y *ᵥ w) = w := fun w => by rw [Matrix.mulVec_mulVec, hBY, Matrix.one_mulVec]
      rw [hK, hmem]
      constructor
      · simp only [Matrix.mulVec_sub, eAX, eAY, sub_self, sub_zero]
      · simp only [Matrix.mulVec_sub, eBX, eBY, sub_self, sub_zero]
    have h3 := hKr ⟨_, hk⟩
    have h1 := hmv X hX (A *ᵥ v)
    have h2 := hmv Y hY (B *ᵥ v)
    have : v = (v - X *ᵥ (A *ᵥ v) - Y *ᵥ (B *ᵥ v)) + X *ᵥ (A *ᵥ v) + Y *ᵥ (B *ᵥ v) := by abel
    have h4 := Submodule.add_mem _ (Submodule.add_mem _ h3 h1) h2
    simp only at h4
    rw [← this] at h4
    exact h4
  have hu : IsUnit C0 := Matrix.mulVec_surjective_iff_isUnit.1 hs
  obtain ⟨C, hC⟩ := hu
  have hCk : ∀ k i, C.1 k i = col i k := fun k i => by rw [hC]; rfl
  refine ⟨C, ?_, ?_, ?_⟩
  · intro i j h k
    have h1 : i.val < m := h ▸ j.2
    rw [hCk]
    simp only [col, dif_pos h1]
    congr 1
    exact Fin.ext h
  · intro i j h k
    have hj := j.2
    have e1 : ¬ (i.val < m) := by omega
    have e2 : ¬ (i.val + m < n) := by omega
    rw [hCk]
    simp only [col, dif_neg e1, dif_neg e2]
    congr 1
    exact Fin.ext (by simp; omega)
  · intro i h1 h2
    have e1 : ¬ (i.val < m) := by omega
    have : (fun k => C.1 k i) = (b ⟨i.val - m, by have := i.2; omega⟩ : K).1 := by
      funext k
      rw [hCk]
      simp only [col, dif_neg e1, dif_pos h2]
    rw [this]
    exact (hmem _).1 (b _).2

theorem exists_isAdapted : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∃ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C := by
  intro D V m X Y hW
  have hyx := GlobalTheory.WittFrame.yx_eq_one D V m X Y hW
  have hxx := hW.xx
  have hyy := hW.yy
  have hxy := hW.xy
  obtain ⟨hle, C, h1, h2, h3⟩ := exists_basis_of_duality X Y
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram)
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram) hyx hyy hxx hxy
  exact ⟨C, ⟨hle, h1, h2, fun i a b => (h3 i a b).2, fun i a b => (h3 i a b).1⟩⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.AdaptedBasis
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

open GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.CompanionTheory.BlockEntry

theorem sandwich_single_apply {A B : Type} [Fintype A] {d : ℕ} (U : Matrix A (Fin d) ℂ) (W : Matrix (Fin d) B ℂ)
    (i j : Fin d) (z : ℂ) (a : A) (c : B) : (U * Matrix.single i j z * W) a c = U a i * z * W j c := by
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_mul, ite_and]

theorem rows_of_adapted {n m : ℕ} {H P : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin m) ℂ}
    (hxx : Xᴴ * H * X = 0) (hyy : Yᴴ * H * Y = 0) (hxy : Xᴴ * H * Y = 1) (hyx : Yᴴ * H * X = 1) (hle : 2 * m ≤ n)
    (cX : ∀ (c : Fin n) (k : Fin m), c.val = k.val → ∀ a, P a c = X a k)
    (cY : ∀ (c : Fin n) (k : Fin m), c.val + k.val + 1 = n → ∀ a, P a c = Y a k)
    (pX : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Xᴴ * H * P) k c = 0)
    (pY : ∀ c : Fin n, m ≤ c.val → c.val + m < n → ∀ k, (Yᴴ * H * P) k c = 0) (k : Fin m) (c : Fin n) :
    (Yᴴ * H * P) k c = (if c.val = k.val then 1 else 0) ∧
      (Xᴴ * H * P) k c = (if c.val + k.val + 1 = n then 1 else 0) := by
  have hk := k.2
  have hc := c.2
  by_cases h1 : c.val < m
  · have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * X) k ⟨c.val, h1⟩ := fun M => by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [cX c ⟨c.val, h1⟩ rfl a]
    rw [e, e, hyx, hxx, Matrix.one_apply, Matrix.zero_apply]
    refine ⟨?_, ?_⟩
    · by_cases e' : c.val = k.val
      · rw [if_pos e', if_pos (Fin.ext e'.symm)]
      · rw [if_neg e', if_neg fun e'' => e' (congrArg Fin.val e'').symm]
    · rw [if_neg (by omega)]
  · by_cases h2 : c.val + m < n
    · rw [pX c (by omega) h2, pY c (by omega) h2, if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    · have hk' : n - 1 - c.val < m := by omega
      have e : ∀ M : Matrix (Fin m) (Fin n) ℂ, (M * P) k c = (M * Y) k ⟨n - 1 - c.val, hk'⟩ := fun M => by
        simp only [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun a _ => by rw [cY c ⟨n - 1 - c.val, hk'⟩ (by simp only; omega) a]
      rw [e, e, hyy, hxy, Matrix.one_apply, Matrix.zero_apply]
      refine ⟨by rw [if_neg (by omega)], ?_⟩
      by_cases e' : c.val + k.val + 1 = n
      · rw [if_pos e', if_pos (Fin.ext (by simp only; omega))]
      · rw [if_neg e', if_neg fun e'' => e' (by have := congrArg Fin.val e''; simp only at this; omega)]

theorem conj_units_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J) {m : ℕ}
    {X Y : Matrix (Fin n) (Fin m) E} (hW : IsWittFrame σ J X Y) {l d : ℕ} (h : l + d ≤ m) {C : GL (Fin n) E}
    (hC : GlobalTheory.BlockForms.IsAdapted σ J X Y C) (τ : E →+* ℂ) (i j : Fin d) (p q p' q' : Fin n)
    (hp : p.val = l + i.val) (hq : q.val = l + j.val) (hp' : p'.val + l + j.val + 1 = n)
    (hq' : q'.val + l + i.val + 1 = n) (z : ℂ) :
    z • (C.1.map τ * Matrix.single p q 1 * (C.1.map τ)⁻¹) -
        (starRingEnd ℂ z) • (C.1.map τ * Matrix.single p' q' 1 * (C.1.map τ)⁻¹) =
      (GlobalTheory.BlockForms.blkCols h X).map τ * Matrix.single i j z * (((GlobalTheory.BlockForms.blkCols h Y).map τ)ᴴ * J.map τ) -
        (GlobalTheory.BlockForms.blkCols h Y).map τ * (Matrix.single i j z)ᴴ * (((GlobalTheory.BlockForms.blkCols h X).map τ)ᴴ * J.map τ) := by
  classical
  set P := C.1.map τ with hP
  have hdet : IsUnit P.det := by
    have e : P.det = τ C.1.det := by rw [hP, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [e]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 C.isUnit).map τ
  obtain ⟨hxx, hyy, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW τ
  have hJh : (J.map τ)ᴴ = J.map τ := GlobalTheory.LeviHC.conjTranspose_map hcm hJ τ
  have hyx := GlobalTheory.CentreFin.dual_swap hJh hxy
  have perp : ∀ (A : Matrix (Fin n) (Fin m) E) (c : Fin n), (Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c) = 0 →
      ∀ k, ((A.map τ)ᴴ * J.map τ * P) k c = 0 := fun A c e k => by
    have e1 : ((Formalism.UG.cT (σ : E →+* E) A * J) *ᵥ (fun k => C.1 k c)) k = 0 := by rw [e]; rfl
    have e2 := congrArg τ e1
    rw [map_zero] at e2
    rw [← e2, ← GlobalTheory.CentreFin.map_cT_emb hcm τ A, ← Matrix.map_mul]

    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  have what₂ := rows_of_adapted (P := P) hxx hyy hxy hyx hC.le
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.colX c k e a, Matrix.map_apply])
    (fun c k e a => by rw [hP, Matrix.map_apply, hC.columnBlock c k e a, Matrix.map_apply])
    (fun c h1 h2 => perp X c (hC.perpX c h1 h2)) (fun c h1 h2 => perp Y c (hC.perpY c h1 h2))
  set Xb := (GlobalTheory.BlockForms.blkCols h X).map τ with hXb
  set Yb := (GlobalTheory.BlockForms.blkCols h Y).map τ with hYb
  set R := Xb * Matrix.single i j z * (Ybᴴ * J.map τ) - Yb * (Matrix.single i j z)ᴴ * (Xbᴴ * J.map τ) with hR
  let f : Fin d → Fin m := fun a => ⟨l + a.val, by omega⟩
  have sY : ∀ (a : Fin d) (c : Fin n), (Ybᴴ * J.map τ * P) a c = if c.val = l + a.val then 1 else 0 := fun a c =>
    (what₂ (f a) c).1
  have sX : ∀ (a : Fin d) (c : Fin n), (Xbᴴ * J.map τ * P) a c = if c.val + (l + a.val) + 1 = n then 1 else 0 := fun a c =>
    (what₂ (f a) c).2
  have hRP : R * P = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) := by
    ext a c
    have e1 : R * P = Xb * Matrix.single i j z * (Ybᴴ * J.map τ * P) -
        Yb * Matrix.single j i (starRingEnd ℂ z) * (Xbᴴ * J.map τ * P) := by
      rw [hR, Matrix.sub_mul, Matrix.conjTranspose_single]
      simp only [Matrix.mul_assoc]
      rfl
    have e2 : P a p = Xb a i := by
      rw [hP, Matrix.map_apply, hC.colX p (f i) hp a]; rfl
    have e3 : P a p' = Yb a j := by
      rw [hP, Matrix.map_apply, hC.columnBlock p' (f j) (by simp only [f]; omega) a]; rfl
    rw [e1, Matrix.sub_apply, sandwich_single_apply, sandwich_single_apply, sY, sX, Matrix.mul_sub, Matrix.sub_apply,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_apply, Matrix.smul_apply]
    have e4 : ∀ (u v : Fin n), (P * Matrix.single u v (1 : ℂ)) a c = P a u * (if c = v then 1 else 0) := fun u v => by
      by_cases e : c = v
      · subst e
        simp [Matrix.mul_single_apply_same]
      · have e' : v ≠ c := fun e'' => e e''.symm
        rw [if_neg e, mul_zero, Matrix.mul_apply]
        exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_apply_of_col_ne _ _ e' _, mul_zero]
    rw [e4, e4, e2, e3]
    have c1 : (c = q) ↔ c.val = l + j.val := by rw [Fin.ext_iff, hq]
    have c2 : (c = q') ↔ c.val + (l + i.val) + 1 = n := by rw [Fin.ext_iff]; omega
    simp only [c1, c2, smul_eq_mul]
    ring
  calc _ = P * (z • Matrix.single p q 1 - (starRingEnd ℂ z) • Matrix.single p' q' 1) * P⁻¹ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    _ = R := by rw [← hRP, Matrix.mul_nonsing_inv_cancel_right _ _ hdet]

theorem lieS_eq_derEnd : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : GlobalTheory.CuspRep.Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
    ∀ (i j : Fin d) (p q p' q' : Fin V.rank), p.val = l + i.val → q.val = l + j.val →
    p'.val + l + j.val + 1 = V.rank → q'.val + l + i.val + 1 = V.rank → ∀ (z : ℂ) (x : GlobalTheory.CuspRep.GA D.host.E d),
      (GlobalTheory.CuspRep.lieS D.host.E d i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) f).1 x =
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
          (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  intro D _ θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' z x
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  obtain ⟨e, he⟩ : ∃ e : EmbOver D.host.E (placeOf D τ), e.1 = tauE D τ := ⟨embOverOf D τ, rfl⟩
  have hline := isLineOf_blockEmb_exp' _ D.host.E D.sp.cm.sig hcm V.rank V.gram hJ m X Y hW l d h ι hι (placeOf D τ)
    e (Matrix.single i j z)
  have hmat := conj_units_eq hcm hJ hW h hC (tauE D τ) i j p q p' q' hp hq hp' hq' z
  rw [he, ← hmat] at hline
  have hsk := hline.skew hcm
  rw [he] at hsk
  have hZ : z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
      (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹) ∈ lieAt V τ := hsk
  have hγ : ∀ t : ℝ, ι (GlobalTheory.CuspRep.infGL D.host.E d (GlobalTheory.CuspRep.expGLi d (t • (Matrix.single i j z).map
      (GlobalTheory.CuspRep.atEmb (tauE D τ))))) = oneP θ V τ (z • (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) -
        (starRingEnd ℂ z) • (C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) t := fun t => by
    obtain ⟨y, e1, e2⟩ := hline t
    refine Eq.trans e1 ?_
    rw [oneP, ← e2, GlobalTheory.Orb.archMat_eq_archEquiv _ hcm, atTau_archEquiv hθ V e he]
  have h0 : GlobalTheory.CuspRep.atEmb (tauE D τ) 0 = 0 := by rw [GlobalTheory.CuspRep.atEmb_eq]; simp
  have hs : Matrix.single i j (GlobalTheory.CuspRep.atEmb (tauE D τ) z) = (Matrix.single i j z).map (GlobalTheory.CuspRep.atEmb (tauE D τ)) := by
    ext a b; simp only [Matrix.single_apply, Matrix.map_apply]; split_ifs <;> simp [h0]
  rw [GlobalTheory.CuspRep.lieS_apply, hs, lie_eq_deriv_exp' D.host.E d f _ x]
  change _ = RderC θ V τ _ F.1 (ι x)
  rw [GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hZ]
  simp only [hf, map_mul, hγ]
  rfl

end GlobalTheory.CompanionTheory.BlockEntry
end
end

section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

theorem _root_.GlobalTheory.T.adapted_basis_conjugate_zero_entries : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ l d : ℕ, l + d ≤ m →
    ∀ C : GL (Fin V.rank) D.host.E, GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C → ∀ (τ : D.what₂.Tau) (p q a b : Fin V.rank),
    (∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ p.val < e ∧ e ≤ q.val) →
    ((C.1.map (tauE D τ))⁻¹ * conjAt V τ (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) * C.1.map (tauE D τ)) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.ConjAdapted.conj_strict | exact GlobalTheory.CompanionTheory.Hypotheses₂.ConjAdapted.conj_strict | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.ConjAdapted.conj_strict <;> assumption)
end

section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.DerGlRel

private theorem commutator_eq_of_glRel {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M)
    (hL : Formalism.REAL.GlRel fun a b : Fin n => L (Matrix.single a b 1))
    (Z W : Matrix (Fin n) (Fin n) ℂ) :
    L Z * L W - L W * L Z = L (Z * W - W * Z) := by
  classical
  have hs : ∀ (i j : Fin n) (x : ℂ),
      (Matrix.single i j x : Matrix (Fin n) (Fin n) ℂ) = x • Matrix.single i j 1 := by
    intro i j x
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have base : ∀ a b c d : Fin n,
      L (Matrix.single a b 1) * L (Matrix.single c d 1) -
          L (Matrix.single c d 1) * L (Matrix.single a b 1) =
        L (Matrix.single a b 1 * Matrix.single c d 1 -
          Matrix.single c d 1 * Matrix.single a b 1) := by
    intro a b c d
    have h := hL a b c d
    simp only at h
    rw [h, map_sub]
    congr 1
    · by_cases h' : b = c
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
    · by_cases h' : d = a
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
  have key1 : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      L Z * L (Matrix.single c d 1) - L (Matrix.single c d 1) * L Z =
        L (Z * Matrix.single c d 1 - Matrix.single c d 1 * Z) := by
    intro Z c d
    refine Matrix.induction_on' Z ?_ ?_ ?_
    · simp
    · intro p q hp hq
      rw [show (p + q) * Matrix.single c d 1 - Matrix.single c d 1 * (p + q) =
          (p * Matrix.single c d 1 - Matrix.single c d 1 * p) +
            (q * Matrix.single c d 1 - Matrix.single c d 1 * q) by noncomm_ring]
      simp only [map_add (f := _)]
      rw [← hp, ← hq]
      noncomm_ring
    · intro i j x
      rw [hs i j x]
      simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, base]
  refine Matrix.induction_on' W ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [show Z * (p + q) - (p + q) * Z = (Z * p - p * Z) + (Z * q - q * Z) by noncomm_ring]
    simp only [map_add (f := _)]
    rw [← hp, ← hq]
    noncomm_ring
  · intro i j x
    rw [hs i j x]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, key1]

theorem glRel_derEnd_family : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Formalism.REAL.GlRel (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) := by
  intro D θ hθ V τ M hM
  unfold Formalism.REAL.GlRel at hM ⊢
  dsimp only at hM ⊢
  intro a b c d
  have h1 := commutator_eq_of_glRel (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ)
    (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) (M a b) (M c d)
  rw [h1, hM a b c d, map_sub]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.DerGlRel

end
end
