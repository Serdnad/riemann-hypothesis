module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prp_of_mem {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K j) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = X := by
  ext a b
  show (if pw a b = j then X a b else 0) = X a b
  split_ifs with h
  · rfl
  · exact (hX a b h).symm

private theorem prp_of_mem_succ {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K)
    (hX : X ∈ adp K (j + 1)) : ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext a b
  show (if pw a b = j then X a b else 0) = 0
  split_ifs with h
  · have hne : ∀ p q : ZMod 2, p = q → p ≠ q + 1 := by decide
    exact hX a b (hne _ _ h)
  · rfl

private theorem prp_add {K : Type} [CommRing K] (j : ZMod 2) (X : Matrix (Fin 3) (Fin 3) K) :
    X = ((prp K j X : adp K j) : Matrix (Fin 3) (Fin 3) K) + (prp K (j + 1) X : adp K (j + 1)) := by
  ext a b
  show X a b = (if pw a b = j then X a b else 0) + (if pw a b = j + 1 then X a b else 0)
  have hc : ∀ p q : ZMod 2, (p = q ∧ p ≠ q + 1) ∨ (p ≠ q ∧ p = q + 1) := by decide
  rcases hc (pw a b) j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg h2, add_zero]
  · rw [if_neg h1, if_pos h2, zero_add]

theorem UpperTheory.V.Fr.ep_prp :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [Field K], (2 : K) ≠ 0 → ∀ (B : Box F 3 K) (π : F.V → Fin 3 → ZMod 2) (h : B.Ev π), (∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X)) ∧ ∀ (j : ZMod 2) (χ : F.Γ → K), (∀ f : Matrix (Fin 3) (Fin 3) K →ₗ[K] K, (∀ g X, f (B.ad g X) = χ g * f X) → f = 0) → ∀ f : adp K j →ₗ[K] K, (∀ g X, f (h.ad j g X) = χ g * f X) → f = 0 := by
  intro l _ k _ F K _ h2 B π h
  have P1 : ∀ j s X, prp K j (B.ad s X) = h.ad j s (prp K j X) := by
    intro j s X
    apply Subtype.ext
    rw [Box.Ev.ad_apply]
    conv_lhs => rw [prp_add j X]
    rw [map_add (f := _), map_add (f := _), Submodule.coe_add,
      prp_of_mem j _ (h.stab j s (prp K j X).2),
      prp_of_mem_succ j _ (h.stab (j + 1) s (prp K (j + 1) X).2), add_zero]
  refine ⟨P1, ?_⟩
  intro j χ hχ f hf
  have hF := hχ (f.comp (prp K j)) (fun g X => by simp only [LinearMap.comp_apply, P1, hf])
  ext v
  have := LinearMap.congr_fun hF (v : Matrix (Fin 3) (Fin 3) K)
  have hv : prp K j (v : Matrix (Fin 3) (Fin 3) K) = v := Subtype.ext (prp_of_mem j _ v.2)
  simpa [hv] using this
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sg_mul_self (R : Type) [CommRing R] (j : ZMod 2) : sg R j * sg R j = 1 := by
  rw [sg, ← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem sg_sub (R : Type) [CommRing R] (i j : ZMod 2) : sg R (i - j) = sg R i * sg R j := by
  have key : ∀ a b : ZMod 2, (a - b).val % 2 = (a.val + b.val) % 2 := by decide
  rw [sg, sg, sg, ← pow_add, neg_one_pow_eq_pow_mod_two, key, ← neg_one_pow_eq_pow_mod_two]

private theorem map_sg {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R) (j : ZMod 2) :
    σ (sg R j) = sg R j := by simp [sg]

private theorem grM_iff {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α β : Fin 3 → ZMod 2) (M : Matrix (Fin 3) (Fin 3) R) :
    GrM σ α β M ↔ σ.mapMatrix M = diagonal (fun a => sg R (α a)) * M * diagonal (fun b => sg R (β b)) := by
  unfold GrM
  rw [← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  change σ (M a b) = sg R (α a - β b) * M a b ↔ _
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, sg_sub]
  constructor <;> intro h <;> rw [h] <;> ring

private theorem diag_sq (R : Type) [CommRing R] (α : Fin 3 → ZMod 2) :
    diagonal (fun a => sg R (α a)) * diagonal (fun a => sg R (α a)) = 1 := by
  rw [diagonal_mul_diagonal]
  simp only [sg_mul_self]
  exact diagonal_one

private theorem map_diag {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (σ : R →ₐ[O] R)
    (α : Fin 3 → ZMod 2) :
    σ.mapMatrix (diagonal (fun a => sg R (α a))) = diagonal (fun a => sg R (α a)) := by
  rw [AlgHom.mapMatrix_apply, Matrix.diagonal_map (map_zero σ)]
  simp only [map_sg]

private theorem exists_sign {R : Type} [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) (x : R) :
    ∃ j : ZMod 2, IsUnit (1 + sg R j * x) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := 1 + x) (b := 1 - x)
      (by convert h2 using 1; ring) with h | h
  · refine ⟨0, ?_⟩
    simpa [sg] using h
  · refine ⟨1, ?_⟩
    rw [show sg R 1 = -1 from by rw [sg, show (1 : ZMod 2).val = 1 from rfl, pow_one]]
    simpa [sub_eq_add_neg] using h

theorem UpperTheory.V.Fr.ep_gflag :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], IsUnit (2 : O) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : R →ₐ[O] R), (∀ y, σ (σ y) = y) → ∀ {H : Type} (r : H → Matrix (Fin 3) (Fin 3) R) (g : GL (Fin 3) R), (∀ s, GrM σ pq pq (r s)) → (∀ s, UpT ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))) → (∀ s i, ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i ∈ evp σ 0) → (∃ s, ∀ i j, i ≠ j → IsUnit (((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i i - ((g : Matrix (Fin 3) (Fin 3) R) * r s * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) j j)) → ∃ (u : GL (Fin 3) R) (α : Fin 3 → ZMod 2), UpT (u : Matrix (Fin 3) (Fin 3) R) ∧ GrM σ α pq ((u * g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  intro O _ _ _ _ h2 R _ _ _ σ hσ H r g hr hT hd hs
  have h2R : IsUnit (2 : R) := by
    have := h2.map (algebraMap O R)
    rwa [map_ofNat] at this
  obtain ⟨s0, hs0⟩ := hs
  have hT0 := hT s0
  have hd0 := hd s0
  set G : Matrix (Fin 3) (Fin 3) R := (g : Matrix (Fin 3) (Fin 3) R) with hGdef
  set Gi : Matrix (Fin 3) (Fin 3) R := ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) with hGidef
  have hGGi : G * Gi = 1 := g.mul_inv
  have hGiG : Gi * G = 1 := g.inv_mul
  set P : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (pq a)) with hPdef
  have hPP : P * P = 1 := diag_sq R pq
  have hσP : σ.mapMatrix P = P := map_diag σ pq
  have hSS : ∀ M : Matrix (Fin 3) (Fin 3) R, σ.mapMatrix (σ.mapMatrix M) = M := by
    intro M
    ext i j
    simp [AlgHom.mapMatrix_apply, hσ]
  have hσr : σ.mapMatrix (r s0) = P * r s0 * P := (grM_iff σ pq pq (r s0)).1 (hr s0)
  have hσGiG : σ.mapMatrix Gi * σ.mapMatrix G = 1 := by rw [← map_mul, hGiG, map_one]
  obtain ⟨h, hh⟩ : ∃ h, h = G * P * σ.mapMatrix Gi := ⟨_, rfl⟩
  have hσh : σ.mapMatrix h = σ.mapMatrix G * P * Gi := by
    rw [hh, map_mul, map_mul, hσP, hSS]
  have hhσh : h * σ.mapMatrix h = 1 := by
    rw [hσh, hh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (σ.mapMatrix Gi), hσGiG, Matrix.one_mul, ← Matrix.mul_assoc P P, hPP,
      Matrix.one_mul, hGGi]
  have hUh : UpT h := by
    set T := G * r s0 * Gi with hTdef
    refine ep_upt h (σ.mapMatrix T) T ?_ hT0 ?_ ?_
    · intro i j hij
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hT0 i j hij, map_zero]
    · intro i j hij
      have hfix : σ (T j j) = T j j := by
        have := hd0 j
        change σ (T j j) = sg R 0 * T j j at this
        rw [this, sg, ZMod.val_zero, pow_zero, one_mul]
      rw [AlgHom.mapMatrix_apply, Matrix.map_apply, hfix]
      exact hs0 j i hij.ne
    · rw [hh, hTdef, map_mul, map_mul, hσr]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (σ.mapMatrix Gi) (σ.mapMatrix G), hσGiG, Matrix.one_mul,
        ← Matrix.mul_assoc P P, hPP, Matrix.one_mul, ← Matrix.mul_assoc Gi G, hGiG, Matrix.one_mul]
  have hex : ∀ i, ∃ j : ZMod 2, IsUnit (1 + sg R j * h i i) := fun i => exists_sign h2R (h i i)
  choose α hα using hex
  set D : Matrix (Fin 3) (Fin 3) R := diagonal (fun a => sg R (α a)) with hDdef
  have hDD : D * D = 1 := diag_sq R α
  have hσD : σ.mapMatrix D = D := map_diag σ α
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 1 + h * D := ⟨_, rfl⟩
  have hYU : Y.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    rw [hY, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), hDdef, Matrix.mul_diagonal,
      hUh i j hij', zero_mul, add_zero]
  have hYdet : IsUnit Y.det := by
    rw [Matrix.det_of_upperTriangular hYU, Fin.prod_univ_three]
    have hu : ∀ i, IsUnit (Y i i) := by
      intro i
      rw [hY, Matrix.add_apply, Matrix.one_apply_eq, hDdef, Matrix.mul_diagonal, mul_comm]
      exact hα i
    exact ((hu 0).mul (hu 1)).mul (hu 2)
  have hYu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).2 hYdet
  set Yi : Matrix (Fin 3) (Fin 3) R := ((hYu.unit⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
    with hYidef
  have hYYi : Y * Yi = 1 := hYu.mul_val_inv
  have hYiY : Yi * Y = 1 := hYu.val_inv_mul
  have hUYi : UpT Yi := by
    haveI : Invertible Y := ⟨Yi, hYiY, hYYi⟩
    have := Matrix.blockTriangular_inv_of_blockTriangular hYU
    rw [Matrix.inv_eq_left_inv hYiY] at this
    exact fun i j hij => this hij
  have hσYσYi : σ.mapMatrix Y * σ.mapMatrix Yi = 1 := by rw [← map_mul, hYYi, map_one]
  have hYeq : h * σ.mapMatrix Y = Y * D := by
    rw [hY, map_add (f := _), map_one, map_mul, hσD, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.one_mul, ← Matrix.mul_assoc, hhσh, Matrix.one_mul, Matrix.mul_assoc, hDD,
      Matrix.mul_one, add_comm]
  have hGP : h * σ.mapMatrix G = G * P := by
    rw [hh, Matrix.mul_assoc, hσGiG, Matrix.mul_one]
  have hYih : Yi * h = D * σ.mapMatrix Yi := by
    calc Yi * h = Yi * (h * (σ.mapMatrix Y * σ.mapMatrix Yi)) := by rw [hσYσYi, Matrix.mul_one]
      _ = Yi * (Y * D) * σ.mapMatrix Yi := by rw [← hYeq]; simp only [Matrix.mul_assoc]
      _ = D * σ.mapMatrix Yi := by rw [← Matrix.mul_assoc Yi Y, hYiY, Matrix.one_mul]
  refine ⟨hYu.unit⁻¹, α, hUYi, ?_⟩
  rw [grM_iff, Units.val_mul]
  change σ.mapMatrix (Yi * G) = D * (Yi * G) * P
  rw [map_mul, Matrix.mul_assoc D, Matrix.mul_assoc Yi, ← hGP, ← Matrix.mul_assoc Yi, hYih,
    Matrix.mul_assoc D, ← Matrix.mul_assoc D D, hDD, Matrix.one_mul]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : UpperTheory.V.Fr.Frame l (ResidueField O)} {n : ℕ}
  (S : Space O F n)

end

theorem UpperTheory.V.Fr.cont_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, S.u.Cont S.x0 ∧ (∀ i, AdicCont S.mB fun g => S.aB g i) ∧ (∀ v i, AdicCont S.mB (S.ψB v i)) ∧ ∀ j (N : ℕ), ∃ M : ℕ, ∀ a ∈ S.gr j, (a : S.R) ∈ maximalIdeal S.R ^ M → a ∈ S.mB ^ N • S.gr j := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := wpres hF hn S
  have hAW : ∀ (j : ℤ) (q : S.R), q ∈ W.part j → q ∈ S.A := by
    intro j q hq
    rw [hA]
    exact Submodule.mem_iSup_of_mem j hq
  have hmulB : ∀ (N : ℕ) (Q : Submodule O S.R),
      (∀ y ∈ Q, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N) →
      ∀ y ∈ Q * W.part 0, ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N Q hQ y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨p', rfl, hp'⟩ := hQ p hp
      have hq0 : q ∈ S.B := (hB q).2 hq
      exact ⟨p' * ⟨q, hq0⟩, rfl, Ideal.mul_mem_right _ _ hp'⟩
    · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
      exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hP : ∀ (N : ℕ) (y : S.R), y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N →
      ∃ b : S.B, (b : S.R) = y ∧ b ∈ S.mB ^ N := by
    intro N
    induction N with
    | zero =>
      intro y hy
      rw [pow_zero, Submodule.mem_one] at hy
      obtain ⟨o, rfl⟩ := hy
      exact ⟨algebraMap O S.B o, rfl, by simp⟩
    | succ N ih =>
      intro y hy
      rw [pow_succ] at hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro p hp q hq
        obtain ⟨p', rfl, hp'⟩ := ih p hp
        have hq0 : q ∈ S.B := (hB q).2 hq.1
        have hqm : (⟨q, hq0⟩ : S.B) ∈ S.mB := by
          show q ∈ maximalIdeal S.R
          exact hq.2
        refine ⟨p' * ⟨q, hq0⟩, rfl, ?_⟩
        rw [pow_succ]
        exact Ideal.mul_mem_mul hp' hqm
      · rintro x z ⟨x', rfl, hx'⟩ ⟨z', rfl, hz'⟩
        exact ⟨x' + z', rfl, Ideal.add_mem _ hx' hz'⟩
  have hT : ∀ (N : ℕ) (j : ℤ) (y : S.R),
      y ∈ (W.part 0 ⊓ Submodule.restrictScalars O (maximalIdeal S.R)) ^ N * W.part 0 * W.part j →
      ∃ a : S.A, (a : S.R) = y ∧ a ∈ S.mB ^ N • S.gr j ∧ a ∈ S.x0 ^ N := by
    intro N j y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro p hp q hq
      obtain ⟨b, rfl, hb⟩ := hmulB N _ (hP N) p hp
      have hqA : q ∈ S.A := hAW j q hq
      refine ⟨b • (⟨q, hqA⟩ : S.A), rfl, Submodule.smul_mem_smul hb ((hgr j ⟨q, hqA⟩).2 hq), ?_⟩
      have hib : S.inc b ∈ S.x0 ^ N := by
        rw [Space.x0, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ hb
      show S.inc b * ⟨q, hqA⟩ ∈ S.x0 ^ N
      exact Ideal.mul_mem_right _ _ hib
    · rintro x z ⟨x', rfl, hx1, hx2⟩ ⟨z', rfl, hz1, hz2⟩
      exact ⟨x' + z', rfl, Submodule.add_mem _ hx1 hz1, Ideal.add_mem _ hx2 hz2⟩
  have hcA : ∀ {Γ : Type} [TopologicalSpace Γ] (j : ℤ) (f : Γ → S.A), (∀ g, (f g : S.R) ∈ W.part j) →
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.x0 f := by
    intro Γ _ j f hf hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    obtain ⟨a, ha, -, ha2⟩ := hT N j _ (hM ⟨Submodule.sub_mem _ (hf y) (hf x), hy⟩)
    have hax : f y - f x = a := Subtype.ext (by rw [ha]; rfl)
    rw [hax]
    exact ha2
  have hcB : ∀ {Γ : Type} [TopologicalSpace Γ] (f : Γ → S.B),
      AdicCont (maximalIdeal S.R) (fun g => (f g : S.R)) → AdicCont S.mB f := by
    intro Γ _ f hc N
    obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz 0 N
    have hcM := hc M
    rw [IsLocallyConstant.iff_eventually_eq] at hcM ⊢
    intro x
    filter_upwards [hcM x] with y hy
    rw [Ideal.Quotient.eq] at hy ⊢
    have hd : ((f y : S.R) - f x) ∈ W.part 0 := (hB _).1 (S.B.sub_mem (f y).2 (f x).2)
    obtain ⟨b, hb, hb2⟩ := hmulB N _ (hmulB N _ (hP N)) _ (hM ⟨hd, hy⟩)
    have hbx : f y - f x = b := Subtype.ext (by rw [hb]; rfl)
    rw [hbx]
    exact hb2
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, fun i => ?_, fun v i => ?_, fun j N => ?_⟩
  · exact hcA (w n i - w n j) (fun g => S.u.r g i j) (fun g => hr g i j) (S.lift.1.1 i j)
  · exact hcA 0 (fun g => (S.u.ψ v i g : S.A)) (fun g => (hB _).1 (S.ψB v i g).2) (S.lift.1.2 v i)
  · exact hcB (fun g => S.aB g i) (S.lift.1.1 i i)
  · exact hcB (S.ψB v i) (S.lift.1.2 v i)
  · obtain ⟨M, hM⟩ := part_filt O ℤ S.R W hz j N
    refine ⟨M, fun a ha hm => ?_⟩
    obtain ⟨b, hb, hb1, -⟩ := hT N j _ (hM ⟨(hgr j a).1 ha, hm⟩)
    have hba : b = a := Subtype.ext hb
    rw [← hba]
    exact hb1
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem isInternal_congr {ι M σ σ' : Type} [DecidableEq ι] [AddCommMonoid M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike σ' M] [AddSubmonoidClass σ' M] (A : ι → σ) (A' : ι → σ')
    (h : ∀ i x, x ∈ A' i ↔ x ∈ A i) (hA : DirectSum.IsInternal A) : DirectSum.IsInternal A' := by
  let e : ∀ i, A' i ≃+ A i := fun i =>
    { toFun := fun x => ⟨x.1, (h i _).1 x.2⟩
      invFun := fun x => ⟨x.1, (h i _).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E : DirectSum ι (fun i => A' i) ≃+ DirectSum ι (fun i => A i) := DFinsupp.mapRange.addEquiv e
  have hE : DirectSum.coeAddMonoidHom A' = (DirectSum.coeAddMonoidHom A).comp E.toAddMonoidHom := by
    refine DirectSum.addHom_ext fun i x => ?_
    have h1 : E (DirectSum.of (fun i => A' i) i x) = DirectSum.of (fun i => A i) i (e i x) :=
      DFinsupp.mapRange_single (hf := fun i => (e i).map_zero)
    show _ = DirectSum.coeAddMonoidHom A (E (DirectSum.of (fun i => A' i) i x))
    rw [h1, DirectSum.coeAddMonoidHom_of, DirectSum.coeAddMonoidHom_of]
    rfl
  unfold DirectSum.IsInternal
  rw [hE]
  exact hA.comp E.bijective

private theorem gr_transfer (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R)
    (hz : ∀ s, W.z s ∈ maximalIdeal R) (B A : Subalgebra O R) [Algebra B A]
    (halg : ∀ b : B, ((algebraMap B A b : A) : R) = b) (gr : ℤ → Submodule B A)
    (hB : ∀ y, y ∈ B ↔ y ∈ W.part 0) (hA : A = W.A) (hgr : ∀ j (a : A), a ∈ gr j ↔ (a : R) ∈ W.part j) :
    DirectSum.IsInternal gr ∧ SetLike.GradedMonoid gr ∧ gr 0 = 1 ∧ (∀ j, (gr j).FG) ∧ Algebra.FiniteType B A ∧
      IsNoetherianRing A := by
  subst hA
  obtain ⟨h1, h2, h3⟩ := gr_noeth O ℤ R W hz
  have h0 : ∀ a : W.A, a ∈ W.gr 0 → ∃ b : B, algebraMap B W.A b = a := fun a ha =>
    ⟨⟨a, (hB _).2 ha⟩, Subtype.ext (halg _)⟩
  refine ⟨isInternal_congr W.gr gr hgr (gr_internal O ℤ R W), ?_, ?_, fun j => ?_, ?_, h1⟩
  · exact
      { one_mem := (hgr _ _).2 (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
        mul_mem := fun _ _ _ _ ha hb => (hgr _ _).2 (SetLike.mul_mem_graded ((hgr _ _).1 ha) ((hgr _ _).1 hb)) }
  · ext a
    rw [Submodule.mem_one, hgr]
    refine ⟨h0 a, ?_⟩
    rintro ⟨b, rfl⟩
    rw [halg]
    exact (hB _).1 b.2
  · obtain ⟨s, hs, hs'⟩ := h3 j
    refine ⟨s, le_antisymm (Submodule.span_le.2 fun a ha => (hgr _ _).2 (hs a ha)) fun a ha => ?_⟩
    have ha' : a ∈ W.gr j := (hgr _ _).1 ha
    rw [hs'] at ha'
    refine Submodule.mul_induction_on ha' (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
    obtain ⟨b, rfl⟩ := h0 x hx
    rw [← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      obtain ⟨b, hb⟩ := h0 _ (SetLike.algebraMap_mem_graded W.gr c)
      rw [Algebra.smul_def, ← hb, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · obtain ⟨s, hs⟩ := h2.out
    refine ⟨⟨s, ?_⟩⟩
    rw [eq_top_iff]
    intro a ht
    clear ht
    have ha : a ∈ Algebra.adjoin (W.gr 0) (s : Set W.A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap r =>
      obtain ⟨b, hb⟩ := h0 r.1 r.2
      have : algebraMap (W.gr 0) W.A r = algebraMap B W.A b := hb.symm
      rw [this]
      exact Subalgebra.algebraMap_mem _ b
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb

theorem UpperTheory.V.Fr.gr_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, DirectSum.IsInternal S.gr ∧ SetLike.GradedMonoid S.gr ∧ S.gr 0 = 1 ∧ (∀ j, (S.gr j).FG) ∧ Algebra.FiniteType S.B S.A ∧ IsNoetherianRing S.A ∧ ∀ g i j, S.u.r g i j ∈ S.gr (w n i - w n j) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, hr, hB, hA, hgr⟩ := UpperTheory.V.Fr.wpres hF hn S
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := gr_transfer O S.R W hz S.B S.A (fun _ => rfl) S.gr hB hA hgr
  exact ⟨h1, h2, h3, h4, h5, h6, fun g i j => (hgr _ _).2 (hr g i j)⟩
end
