module

public import ReciprocityTheory.DualLattices.Bundle006
public import ReciprocityTheory.DualLattices.Bundle008
public import ReciprocityTheory.DualLattices.Bundle017
public import ReciprocityTheory.DualLattices.Bundle018
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties
public import ReciprocityTheory.DualLattices.MemDualLatMapFourier
public import ReciprocityTheory.DualLattices.Bundle004
import ReciprocityTheory.DualLattices.Bundle009
import ReciprocityTheory.DualLattices.Bundle011
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (AlgHom.ext h)

lemma isHeight_map (hB1 : PairingPropertiesStatement B) {R S : LAlg R₀} (Dp : DualPair R) (Dq : DualPair S)
    (g : LHom R S) (f : LHom Dp.D Dq.D) (hfπ : ∀ x, Dq.π.1 (f.1 x) = g.1 (Dp.π.1 x))
    (hfσ : ∀ x, f.1 (Dp.σ.1 x) = Dq.σ.1 (g.1 x)) (hfη : f.1 Dp.η = Dq.η) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (H : B.IsHeight Dp N y h) :
    B.IsHeight Dq N (B.map g y) (g.1.toLinearMap ∘ₗ h) := by
  obtain ⟨-, -, -, -, -, -, hnat, -⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨Units.map (f.1 : (Dp.D : Type u) →* Dq.D) z, ?_, ?_⟩
  · have h1 := hnat _ _ f N _ _ z hz
    have hf : ∀ a ∈ Dp.π.ker, f.1.toLinearMap a ∈ Dq.π.ker := by
      intro a ha
      rw [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
      change Dq.π.1 (f.1 a) = 0
      rw [hfπ, ha, map_zero]
    have e1 : B.map f (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) = B.tg Dq.π Dq.sqZero (v ⊗ₜ Dq.ηk) := by
      rw [← B.tg_nat Dp.π Dq.π Dp.sqZero Dq.sqZero f hf, LinearMap.lTensor_tmul]
      congr 2
      exact Subtype.ext hfη
    have e2 : B.map f (B.map Dp.σ y) = B.map Dq.σ (B.map g y) := by
      have hc : f.comp Dp.σ = Dq.σ.comp g := lhom_ext fun x => hfσ x
      rw [← B.map_comp, ← B.map_comp, hc]
    rw [e1, e2] at h1
    exact h1
  · simp only [Units.coe_map, MonoidHom.coe_coe, hze, map_add (f := _), map_one, map_mul, hfσ, hfη]
    rfl

lemma nsmul_tg_eta {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (hN : (N : (R : Type u)) = 0) (v : B.gg) :
    N • B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk) = 0 := by
  rw [← map_nsmul, ← tmul_smul]
  have : N • Dp.ηk = 0 := by
    apply Subtype.ext
    change N • Dp.η = 0
    rw [nsmul_eq_mul, ← map_natCast Dp.σ.1, hN, map_zero, zero_mul]
  rw [this, tmul_zero, map_zero]

lemma isHeight_mul_p (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N p : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : (N * p) • y = 0) (h : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp (N * p) y h) : B.IsHeight Dp N (p • y) h := by
  obtain ⟨-, -, -, -, -, -, -, hNp⟩ := hB1
  intro v
  obtain ⟨z, hz, hze⟩ := H v
  refine ⟨z, ?_, hze⟩
  have h1 := hNp _ N p _ _ z (B.nsmul_tg_eta Dp N hN v) (by rw [← map_nsmul, hy, map_zero]) hz
  rwa [← map_nsmul] at h1

lemma isHeight_unique (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) (h h' : B.gg →ₗ[R₀] (R : Type u))
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y h') : h = h' :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).unique H H'

lemma isHeight_exists (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) (y : B.G R) (hy : N • y = 0) :
    ∃ h, B.IsHeight Dp N y h :=
  ((heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.1 y hy).exists

lemma isHeight_add (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y y' : B.G R} {h h' : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (H' : B.IsHeight Dp N y' h') : B.IsHeight Dp N (y + y') (h + h') :=
  (heightFunctionalStatement_of_pairingProperties B hB1 R Dp N hN).2.2 y y' h h' H H'

lemma isHeight_zero (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) : B.IsHeight Dp N 0 0 := by
  obtain ⟨h, hh⟩ := B.isHeight_exists hB1 Dp N hN 0 (smul_zero N)
  have h2 := B.isHeight_add hB1 Dp N hN hh hh
  rw [add_zero] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ hh h2
  have h4 : h = 0 := by
    have := congrArg (fun k => k - h) h3
    simpa using this.symm
  rwa [h4] at hh

lemma isHeight_neg (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) : B.IsHeight Dp N (-y) (-h) := by
  obtain ⟨h', hh'⟩ := B.isHeight_exists hB1 Dp N hN (-y) (by rw [smul_neg, hy, neg_zero])
  have h2 := B.isHeight_add hB1 Dp N hN H hh'
  rw [add_neg_cancel] at h2
  have h3 := B.isHeight_unique hB1 Dp N hN 0 (smul_zero N) _ _ h2 (B.isHeight_zero hB1 Dp N hN)
  have h4 : h' = -h := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h3
  rwa [h4] at hh'

lemma isHeight_zsmul (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {y : B.G R} (hy : N • y = 0) {h : B.gg →ₗ[R₀] (R : Type u)}
    (H : B.IsHeight Dp N y h) (k : ℤ) : B.IsHeight Dp N (k • y) (k • h) := by
  have hnat : ∀ m : ℕ, B.IsHeight Dp N (m • y) (m • h) := by
    intro m
    induction m with
    | zero => simpa using B.isHeight_zero hB1 Dp N hN
    | succ m ih => rw [succ_nsmul, succ_nsmul]; exact B.isHeight_add hB1 Dp N hN ih H
  rcases k with m | m
  · simpa using hnat m
  · have hm : N • ((m + 1) • y) = 0 := by rw [smul_comm, hy, smul_zero]
    have := B.isHeight_neg hB1 Dp N hN hm (hnat (m + 1))
    simpa [negSucc_zsmul] using this

lemma isHeight_sum (hB1 : PairingPropertiesStatement B) {R : LAlg R₀} (Dp : DualPair R) (N : ℕ)
    (hN : (N : (R : Type u)) = 0) {ι : Type} (s : Finset ι) (y : ι → B.G R) (hy : ∀ i, N • y i = 0)
    (h : ι → B.gg →ₗ[R₀] (R : Type u)) (H : ∀ i, B.IsHeight Dp N (y i) (h i)) :
    B.IsHeight Dp N (∑ i ∈ s, y i) (∑ i ∈ s, h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using B.isHeight_zero hB1 Dp N hN
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact B.isHeight_add hB1 Dp N hN (H a) ih

end BX

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.L2

theorem h1 (C R : Type) [Field C] [CommRing R] [Algebra R C] :
    DualHopfOrderStatement (C := C) (R := R) := by
  intro v hv N H _ _ _ _ _ _ e he hcard AA
  obtain ⟨B, hB, hAA⟩ := AA.lat
  have σ : H ≃ N := Fintype.equivOfCardEq hcard
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix H H C,
      M = ((tableM e σ)ᵀ * (B⁻¹)ᵀ).submatrix σ σ := ⟨_, rfl⟩
  have hdual : dualLat AA.carrier = Submodule.span R (Set.range fun j x => (B⁻¹)ᵀ x j) := by
    rw [hAA]; exact dualLat_spanCols B hB
  have hmap : (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => M h k) := by
    rw [hdual, hMdef]; exact map_fourier_spanCols e σ _
  have hBB : B.det * B⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv B hB, Matrix.det_one]
  have hBinv : IsUnit B⁻¹.det := ⟨⟨B⁻¹.det, B.det, by rw [mul_comm]; exact hBB, hBB⟩, rfl⟩
  have hdetM : M.det = (tableM e σ).det * B⁻¹.det := by
    rw [hMdef, Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_transpose]
  have hMunit : IsUnit M.det := by
    rw [hdetM]; exact (tableM_isUnit e σ).mul hBinv
  have hdd : dualLat (dualLat AA.carrier) = AA.carrier := by
    rw [hAA]; exact dualLat_dualLat_spanCols B hB
  refine ⟨{ carrier := (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a)
            lat := ⟨M, hMunit, hmap⟩
            le_int := by
              rintro w ⟨u, hu, rfl⟩ h
              exact hv.exists_of_le_one (valuation_fourier_le_one v hv (fun h => e h) AA hu h)
            one_mem := Submodule.mem_map.mpr ⟨(Pi.single 0 1 : N → C),
              single_mem_dualLat AA,
              funext fun h => fourier_single (R := R) (fun h => e h) h⟩
            mul_mem := by
              rintro f g ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
              exact Submodule.mem_map.mpr ⟨conv u w,
                conv_mem_dualLat AA hu hw,
                funext fun h => fourier_conv (R := R) (fun h => e h) u w h⟩
            comul := by
              rintro f ⟨u, hu, rfl⟩
              exact comul_fourier e he AA B hB hAA u hu
            antipode := by
              rintro f ⟨u, hu, rfl⟩
              exact antipode_fourier e he AA u hu }, rfl, ?_, ?_⟩
  · ext f
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h1 := (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mp hw
      rwa [hdd] at h1
    · intro hf
      obtain ⟨w, hw⟩ := fourier'_surjective (R := R) e σ f
      refine ⟨w, (mem_dualLat_map_fourier e (dualLat AA.carrier) w).mpr ?_, hw⟩
      rw [hw, hdd]; exact hf
  · intro c c' hc hc'
    obtain ⟨B₀, hB₀, rfl⟩ := hc
    obtain ⟨B₁, hB₁, rfl⟩ := hc'
    have e0 : v B₀.det = v B.det :=
      valuation_det_eq_of_span_eq v hv B₀ B (hB₀.symm.trans hAA)
    have e1 : v B₁.det = v M.det :=
      valuation_det_eq_of_span_eq v hv B₁ M (hB₁.symm.trans hmap)
    have key : v B.det * v M.det = v (tableM e σ).det := by
      rw [← map_mul, hdetM, mul_left_comm, hBB, mul_one]
    have h2 : (tableM e σ).det ^ 2 = (Fintype.card N : C) ^ Fintype.card N ∨
        (tableM e σ).det ^ 2 = -(Fintype.card N : C) ^ Fintype.card N :=
      ReciprocityTheory.PGsh.charTable C N (σ.symm.trans e)
    rw [e0, e1, key]
    calc v (tableM e σ).det ^ 2 = v ((tableM e σ).det ^ 2) :=
          (map_pow v _ 2).symm
      _ = v (Fintype.card N : C) ^ Fintype.card N := by
        rcases h2 with h | h <;> rw [h] <;> simp [Valuation.map_neg, map_pow]

end ReciprocityTheory.PGsh.L2
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EigenQuotientSmithStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ X : NNReal, HasLen v R (xMod H e π w) X →
    ∃ (Λ : Matrix (Fin r) (Fin r) R) (dj : Fin r → R), IsUnit Λ.det ∧
      (∀ j, dj j • Λ j ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i)) ∧
      (∀ j, v (algebraMap R C cp) ≤ v (algebraMap R C (dj j))) ∧
      X = ∏ j, v (algebraMap R C (dj j))

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def psiW {p : ℕ} [Fact p.Prime] {g r : ℕ} (Bw : Matrix (Ix g) (Fin r) ℤ_[p]) :
    (Fin r → ZMod p) →+ Nb p g :=
  (Matrix.mulVecLin (Bw.map PadicInt.toZMod)).toAddMonoidHom

def RestrictedHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (a : O), a * a = a →
    ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ a)) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (H.ρL a)) ≃ₗ[R] (Fin d → R)) →
    ∃ AW : HopfOrder (C := C) R (Fin r → ZMod p),
      AW.carrier = H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)) ∧
      HasLen v R (OmAA AW.carrier) (v (algebraMap R C (p : R)) ^ d)

def RestrictedHopfOrderApproximationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ (lam : Fin r → R) (dj : R),
      dj • lam ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i) →
      v (algebraMap R C cp) ≤ v (algebraMap R C dj) →
      ∃ f ∈ H.AA.carrier.map (LinearMap.funLeft R C (psiW Bw)), ∀ x : Fin r → ℤ_[p],
        v (f (fun i => PadicInt.toZMod (x i)) -
          algebraMap R C (dj * ∑ i, lam i * algebraMap ℤ_[p] R (x i))) < v (algebraMap R C dj)

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Defs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def bt2 (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H) : Matrix (Fin g) (Ix g) R :=
  ∑ i, U.εL i * H.Bt * U.εT i

end Defs

def EigenLengthProductStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    ∀ X : Fin m → NNReal, (∀ i, HasLen v R (xModE Ht Bt εT εL π i) (X i)) →
      ∏ i, X i = v (algebraMap R C (fromRows Ht Bt).det)

def EigenLengthFrobeniusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∏ i, X i = v (algebraMap R C cp) ^ g →
    ∀ i, X i ^ p ≤ X (U.φ i) * v (algebraMap R C (p : R)) ^ U.r (U.φ i)

end ReciprocityTheory.PGsh.Up
end
end
