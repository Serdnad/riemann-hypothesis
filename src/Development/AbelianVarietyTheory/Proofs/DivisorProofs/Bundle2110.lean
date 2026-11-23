module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousLvMat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.FrameCompl

variable {E : Type} [Field E]

theorem cT_mul (τ : E →+* E) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_add (τ : E →+* E) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i k; simp [cT]

theorem cT_cT (τ : E →+* E) (hτ : ∀ x, τ (τ x) = x) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i k; simp [cT, hτ]

theorem cT_one (τ : E →+* E) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) E) = 1 := by
  ext i k; simp [cT, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]

theorem cT_zero (τ : E →+* E) {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i k; simp [cT]

end GlobalTheory.SphEis.FrameCompl


open GlobalTheory.SphEis.FrameCompl in
theorem GlobalTheory.SphEis.exists_fr_of_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (j : ℕ) (C D : Matrix (Fin n) (Fin j) E), cT (σ : E →+* E) C * J * C = 0 → cT (σ : E →+* E) D * J * D = 0 → cT (σ : E →+* E) C * J * D = 1 → ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ := by
  intro F E _ _ _ _ _ σ hcm n J hJ j C D hcc hdd hcd
  set τ : E →+* E := (σ : E →+* E) with hτdef
  have hτ : ∀ x, τ (τ x) = x := fun x => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm x
  have hJJ : cT τ J = J := by ext i k; exact hJ.1 i k
  have hdc : cT τ D * J * C = 1 := by
    have := congrArg (cT τ) hcd
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_one, ← Matrix.mul_assoc] at this

  let W : Submodule E (Fin n → E) :=
    LinearMap.ker (Matrix.toLin' (cT τ C * J)) ⊓ LinearMap.ker (Matrix.toLin' (cT τ D * J))
  let m := Module.finrank E W
  let b : Module.Basis (Fin m) E W := Module.finBasis E W
  let Z : Matrix (Fin n) (Fin m) E := Matrix.of fun r k => (b k : Fin n → E) r
  have hZv : ∀ u : Fin m → E, Z *ᵥ u = ((∑ k, u k • b k : W) : Fin n → E) := by
    intro u; ext r
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hk : ∀ k, Z *ᵥ Pi.single k 1 = (b k : Fin n → E) := by
    intro k; rw [hZv]; simp [Pi.single_apply]
  have hCZ : cT τ C * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.1
  have hDZ : cT τ D * J * Z = 0 := by
    apply Matrix.ext_of_mulVec_single; intro k
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec, hk]
    exact (b k).2.2
  have hZC : cT τ Z * J * C = 0 := by
    have := congrArg (cT τ) hCZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this
  have hZD : cT τ Z * J * D = 0 := by
    have := congrArg (cT τ) hDZ
    rwa [cT_mul, cT_mul, cT_cT τ hτ, hJJ, cT_zero, ← Matrix.mul_assoc] at this

  set Pr : Matrix (Fin n) (Fin n) E := 1 - C * (cT τ D * J) - D * (cT τ C * J) with hPr
  have hCPr : cT τ C * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hcc, hcd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hDPr : cT τ D * J * Pr = 0 := by
    simp only [hPr, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hdc, hdd, Matrix.zero_mul, Matrix.one_mul]
    abel
  have hmem : ∀ i, Pr *ᵥ Pi.single i 1 ∈ W := by
    intro i
    refine ⟨?_, ?_⟩
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hCPr, Matrix.zero_mulVec]
    · show Matrix.toLin' _ _ = 0
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hDPr, Matrix.zero_mulVec]
  let M : Matrix (Fin m) (Fin n) E := Matrix.of fun k i => b.repr ⟨_, hmem i⟩ k
  have hZM : Z * M = Pr := by
    apply Matrix.ext_of_mulVec_single; intro i
    rw [← Matrix.mulVec_mulVec]
    have : M *ᵥ Pi.single i 1 = fun k => b.repr ⟨_, hmem i⟩ k := by
      ext k; simp [M, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [this, hZv, b.sum_repr]
  have hdec : C * (cT τ D * J) + D * (cT τ C * J) + Z * M = 1 := by
    rw [hZM, hPr]; abel

  set J₀ : Matrix (Fin m) (Fin m) E := cT τ Z * J * Z with hJ₀
  have hJ₀h : cT τ J₀ = J₀ := by
    rw [hJ₀, cT_mul, cT_mul, cT_cT τ hτ, hJJ, Matrix.mul_assoc]
  have hCZ' : cT τ C * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hCZ
  have hDZ' : cT τ D * (J * Z) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hDZ
  have key : J * Z = cT τ M * J₀ := by
    have h1 : cT τ (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) = 1 := by rw [hdec, cT_one]
    rw [cT_add, cT_add, cT_mul, cT_mul, cT_mul, cT_mul, cT_mul, cT_cT τ hτ, cT_cT τ hτ, hJJ] at h1
    conv_lhs => rw [← Matrix.one_mul (J * Z), ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', Matrix.mul_zero, zero_add, hJ₀]
  have hdet : J₀.det ≠ 0 := by
    intro h0
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hJz : J *ᵥ (Z *ᵥ u) = 0 := by
      rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    have hz := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hJz
    rw [hZv] at hz
    have hs : (∑ k, u k • b k : W) = 0 := Subtype.ext hz
    exact hu0 (funext fun k => Fintype.linearIndependent_iff.mp b.linearIndependent u hs k)
  have hinv : J₀⁻¹ * J₀ = 1 := Matrix.nonsing_inv_mul J₀ (isUnit_iff_ne_zero.mpr hdet)
  set S : Matrix (Fin n) (Fin n) E := C * (cT τ D * J) + Z * (J₀⁻¹ * (cT τ Z * J)) + D * (cT τ C * J) with hS
  have a1 : cT τ D * (J * C) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hdc
  have a2 : cT τ Z * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZC
  have a3 : cT τ C * (J * C) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hcc
  have a4 : cT τ D * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hdd
  have a5 : cT τ Z * (J * D) = 0 := (Matrix.mul_assoc _ _ _).symm.trans hZD
  have a6 : cT τ C * (J * D) = 1 := (Matrix.mul_assoc _ _ _).symm.trans hcd
  have a7 : cT τ Z * (J * Z) = J₀ := (Matrix.mul_assoc _ _ _).symm
  have hSC : S * C = C := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a1, a2, a3, Matrix.mul_zero, Matrix.mul_one, add_zero]
  have hSD : S * D = D := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, a4, a5, a6, Matrix.mul_zero, Matrix.mul_one, zero_add]
  have hSZ : S * Z = Z := by
    simp only [hS, Matrix.add_mul, Matrix.mul_assoc, hCZ', hDZ', a7, Matrix.mul_zero, add_zero, zero_add]
    rw [hinv, Matrix.mul_one]
  have hS1 : S = 1 := by
    calc S = S * (C * (cT τ D * J) + D * (cT τ C * J) + Z * M) := by rw [hdec, Matrix.mul_one]
      _ = S * C * (cT τ D * J) + S * D * (cT τ C * J) + S * Z * M := by
          simp only [Matrix.mul_add, Matrix.mul_assoc]
      _ = 1 := by rw [hSC, hSD, hSZ, hdec]
  have hdim : m + 2 * j = n := by
    have ht := congrArg Matrix.trace hS1
    rw [hS, Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm C, Matrix.trace_mul_comm Z,
      Matrix.trace_mul_comm D] at ht
    simp only [Matrix.mul_assoc, a1, a6, a7, hinv, Matrix.trace_one, Fintype.card_fin] at ht
    have : ((m + 2 * j : ℕ) : E) = (n : E) := by push_cast; rw [← ht]; ring
    exact_mod_cast this
  refine ⟨m, Z, J₀, hcm, hJ, ⟨fun i k => ?_, hdet⟩, hcc, hdd, hcd, hdc, hCZ, hDZ, hZC, hZD, rfl, hS1, hdim⟩
  have := congrFun (congrFun hJ₀h i) k
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply] at this
  exact this
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem mem_unipRad_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr u
  have hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    simp only [adMat]; exact Matrix.map_mul
  have hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) =
      adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
    have e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) =
        C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
      rw [← fr.sum]; abel
    rw [e, ← hmap, ← hmap]
    simp only [adMat]; exact Matrix.map_add _ (map_add _) _ _
  have hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]
  have hdual : u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin j) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J u).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
    constructor
    · intro hg
      simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
        sub_eq_iff_eq_add, zero_add]
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨h1, -, h3⟩ := hg
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, fr.cd, Matrix.mul_one, Matrix.one_mul, sub_self]
        choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
          (funext fun j => congrFun (congrFun hT j) k)
        refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
        rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
        ext i k
        exact congrFun (ha k) i
      | one => exact ⟨by simp, 0, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a1, A, a2⟩ := ha
        obtain ⟨b1, B, b2⟩ := hb
        refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
        rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
          add_assoc]
      | inv a _ ha =>
        obtain ⟨a1, A, a2⟩ := ha
        have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
          conv_lhs => rw [← a1]
          rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        refine ⟨i1, -A, ?_⟩
        have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
        rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
          inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
        rw [Matrix.mul_neg]
        conv_rhs => rw [this]
        abel
    · rintro ⟨h1, B, h2⟩
      refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
      · have hg : cT (sigR (AF F) σ) (matHom _ σ J u).1 * adMat F J * (matHom _ σ J u).1 = adMat F J := u.2
        have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
        conv_lhs => rw [← h1, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J u).1)]
        exact congrArg _ hg
      · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
            fun i => inclR (F := F) (AF F) (x i) := by
          funext i
          have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
          rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
          exact this.symm
        rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]
  rw [hdual]
  set M := (matHom _ σ J u).1
  constructor
  · rintro ⟨h1, B, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩
    have := congrArg (· * adMat F Z) h2
    rw [Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc] at this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rintro ⟨h1, b, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩
    have h1' : (M - 1) * adMat F C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    have h2' : (M - 1) * adMat F Z = adMat F C * b := by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]

end GlobalTheory.SphEis
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem eq_of_frame_cols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g g' : GAd σ J, (matHom _ σ J g).1 * adMat F C = (matHom _ σ J g').1 * adMat F C → (matHom _ σ J g).1 * adMat F Z = (matHom _ σ J g').1 * adMat F Z → (matHom _ σ J g).1 * adMat F D = (matHom _ σ J g').1 * adMat F D → g = g' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g g' hC hZ hD
  have key : ∀ h : GAd σ J, (matHom _ σ J h).1 =
      (matHom _ σ J h).1 * adMat F C * adMat F (cT (σ : E →+* E) D * J) +
      (matHom _ σ J h).1 * adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (matHom _ σ J h).1 * adMat F D * adMat F (cT (σ : E →+* E) C * J) := by
    intro h
    have e : (matHom _ σ J h).1 = (matHom _ σ J h).1 * adMat F (C * (cT (σ : E →+* E) D * J) +
        Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + D * (cT (σ : E →+* E) C * J)) := by
      rw [hF.sum, adMat, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    conv_lhs => rw [e]
    simp only [adMat, Matrix.map_add (inclR (F := F) (E := E) (AF F)) (map_add _), Matrix.map_mul, Matrix.mul_add, Matrix.mul_assoc]
  apply matHom_injective _ σ J
  apply Units.ext
  rw [key g, key g', hC, hZ, hD]

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isLv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ f
  exact ⟨GlobalTheory.SphEisModel.lv f, GlobalTheory.SphEisModel.isLv_lv f⟩

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem cover_rect_adMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  intro F E _ _ _ _ _ σ hσ j m
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.GodementSectionReduction.cover_adele F E σ hσ
  choose Y hY h using h
  refine ⟨Ω, (C ^ m) ^ j, hΩ, fun μ =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i)).card = ∏ i, (Y (μ i)).card ^ m := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (μ i)) m).trans (le_of_eq ?_)
    simp only [bse, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul _ (μ _), mul_comm m]
  · choose x₀ y hy ω hω e using fun i k => h (μ i) (x i k)
    refine ⟨Matrix.of x₀, Matrix.of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), Matrix.of ω,
      fun i k => hω i k, ?_⟩
    ext i k
    rw [Matrix.add_apply, Matrix.add_apply, ← add_assoc]
    simp only [tor, GlobalTheory.Eis.Conv.dg, Matrix.diagonal_mul, adMat, Matrix.map_apply, Matrix.of_apply, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact e i k

end GlobalTheory.SphEis

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem det_upU {K : Type} [Field K] {s : ℕ} (y : Low s → K) : (upU y).det = 1 := by
  have hb : (upU y).BlockTriangular id := fun a b (hab : b < a) => by
    simp only [upU, Matrix.of_apply, dif_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => by simp [upU]

theorem pts_of {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hR : Refines E E' φ f) {A : Mat m X.Fn}
    {u : Cell m → Y.Fn} (hg : InCell E E' φ f A u (genericPoint Y.X)) {K : Type} [Field K] (x : Sp K ⟶ X.X)
    (hA : A ∈ E.S (x (IsLocalRing.closedPoint K))) (y₀ : Cell m → K)
    (hbears : ∀ p : Sp K ⟶ Y.X, A ∈ E.S (f (p (IsLocalRing.closedPoint K))) →
      (Bears E' φ A (upM y₀) p ↔ ∃ u' : Cell m → Y.Fn, upM u' * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, (ratOf Y).val p (u' j) = y₀ j))
    (huniq : ∀ (s : ℕ) (y y' : Low s → Y.Fn) (b : Matrix (Fin s) (Fin s) Y.Fn), (∀ i j, i < j → b i j = 0) →
      upU y = b * upU y' → y = y') :
    ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧
      ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  have hPar : Par 0 ⊤ (upM y₀) := fun τ =>
    ⟨fun _ _ => trivial, by simp [upM, det_upU], trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨p, ⟨hpf, hpB⟩, huq⟩ := hR.lifts K x A hA (upM y₀) hPar
  have hfz : f (p (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
    rw [← hpf]; rfl
  have hA' : A ∈ E.S (f (p (IsLocalRing.closedPoint K))) := hfz ▸ hA
  obtain ⟨u', hu'S, hu'v⟩ := (hbears p hA').1 hpB
  have huu : u' = u := by
    have h1 := Fr.mem_genericPoint hu'S
    have hdA : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
      have := Mat.det_map A φ.toRingHom τ
      rw [show A.map φ.toRingHom = A.map φ from rfl] at this
      rw [this]; exact (map_ne_zero _).2 (Fr.det_ne hg.1 τ)
    have hdu : ∀ τ, (upM u τ).det ≠ 0 := fun τ => by simp [upM, det_upU]
    have hP := (Fr.mem_iff hg.2).1 h1
    rw [Mat.mul_inv_rev, ← mul_assoc, mul_assoc (upM u'), Mat.mul_inv hdA, mul_one] at hP
    have he : upM u' = (upM u' * (upM u)⁻¹) * upM u := by rw [mul_assoc, Mat.inv_mul hdu, mul_one]
    funext ⟨τ, s⟩
    have := huniq (m τ) (fun s => u' ⟨τ, s⟩) (fun s => u ⟨τ, s⟩) ((upM u' * (upM u)⁻¹) τ)
      (fun i j hij => (hP τ).2.2.2 i j i.2 hij) (congrFun he τ)
    exact congrFun this s
  subst huu
  refine ⟨p, ⟨hpf, ⟨hA', hu'S⟩, hu'v⟩, fun p' ⟨hp'f, ⟨h1, h2⟩, hv⟩ => huq p' ⟨hp'f, (hbears p' h1).2 ⟨u', h2, hv⟩⟩⟩

theorem cell_points_existsUnique : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hR A u hg K _ x hA y₀
  exact pts_of hR hg x hA y₀ (fun p hp => GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A K p hp y₀)
    (fun s y y' b hb h => upU_unique_of_lower Y.Fn s y y' b hb h)

end GlobalTheory.FlagCell2
end
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.pullback_base_form_flag_cell_coordinates : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (α : (atlas X σ).Fld), (atlas X σ).IsForm α → ∀ x : (atlas Y σ).Pt, x.pt ∈ cellSet E E' φ f hf c A u → (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α x = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (pull (bsL ε) ((atlas X σ).loc α c (bsL ε (cellMap ε f hf c u x.pt)))) := by
  first | exact @GlobalTheory.FlagCell2.pullback_cell | exact GlobalTheory.FlagCell2.pullback_cell | (intros; apply GlobalTheory.FlagCell2.pullback_cell <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.graded_line_first_chern_forms_pullback_cell : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m) (x : (atlas Y σ).Pt), x.pt ∈ cellSet E E' φ f hf c A u → ∀ r : Root m, (grF E' (pullGram E H φ f hf) r x : Alt Y.dim) = pull (fderiv ℂ (cellMap ε f hf c u ∘ x.ch.symm) x.crd) (ofValues (ddc (cellPot ε (fun v => H A (c.e.symm v)) r) (cellMap ε f hf c u x.pt)) : Ev Y.dim) := by
  first | exact @GlobalTheory.FlagCell2.GradedPull.grF_eq_pull | exact GlobalTheory.FlagCell2.GradedPull.grF_eq_pull | (intros; apply GlobalTheory.FlagCell2.GradedPull.grF_eq_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem _root_.GlobalTheory.T.topDegreeDensity_base_form_times_fibre_class : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n), (∀ τ, (G (bsL ε w) τ).PosDef) → (∀ τ, MContDiffAt 2 (fun v => G v τ) (bsL ε w)) → dens (cellForm ε G a w) = dens (a (bsL ε w)) * (fibDens (G (bsL ε w)) (fb ε w) : ℝ) := by
  first | exact @GlobalTheory.FlagCell2.CellDens.dens_cellForm | exact GlobalTheory.FlagCell2.CellDens.dens_cellForm | (intros; apply GlobalTheory.FlagCell2.CellDens.dens_cellForm <;> assumption)
end
