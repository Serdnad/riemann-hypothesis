module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle324
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem cT_add' {a b : Type} (M N : Matrix a b S) : cT s (M + N) = cT s M + cT s N := by
  ext i k; simp [cT]

theorem cT_zero' {a b : Type} : cT s (0 : Matrix a b S) = 0 := by
  ext i k; simp [cT]

theorem cT_cT' (hs : ∀ x, s (s x) = x) {a b : Type} (M : Matrix a b S) : cT s (cT s M) = M := by
  ext i k; simp [cT, hs]

theorem cT_gram {n a b : ℕ} (hs : ∀ x, s (s x) = x) (J : Matrix (Fin n) (Fin n) S) (hJ : cT s J = J)
    (M : Matrix (Fin n) (Fin a) S) (N : Matrix (Fin n) (Fin b) S) :
    cT s (cT s M * J * N) = cT s N * J * M := by
  rw [cT_mul, cT_mul, cT_cT' s hs, hJ, Matrix.mul_assoc]

theorem gram_comb {n j m : ℕ} (J : Matrix (Fin n) (Fin n) S) (J0 : Matrix (Fin m) (Fin m) S)
    (A B : Matrix (Fin n) (Fin j) S) (Z : Matrix (Fin n) (Fin m) S)
    (pX pY : Matrix (Fin j) (Fin n) S) (p0 : Matrix (Fin m) (Fin n) S)
    (aa : cT s A * J * A = 0) (bb : cT s B * J * B = 0) (ab : cT s A * J * B = 1) (ba : cT s B * J * A = 1)
    (az : cT s A * J * Z = 0) (bz : cT s B * J * Z = 0) (za : cT s Z * J * A = 0) (zb : cT s Z * J * B = 0)
    (zz : cT s Z * J * Z = J0) :
    cT s (A * pX + Z * p0 + B * pY) * J * (A * pX + Z * p0 + B * pY) =
      cT s pX * pY + cT s p0 * J0 * p0 + cT s pY * pX := by
  have h1 : cT s A * (J * (A * pX + Z * p0 + B * pY)) = pY := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, aa, az, ab, Matrix.zero_mul, Matrix.one_mul, zero_add]
  have h2 : cT s Z * (J * (A * pX + Z * p0 + B * pY)) = J0 * p0 := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, za, zz, zb, Matrix.zero_mul, zero_add, add_zero]
  have h3 : cT s B * (J * (A * pX + Z * p0 + B * pY)) = pX := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, ba, bz, bb, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero]
  rw [cT_add', cT_add', cT_mul, cT_mul, cT_mul]
  simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_invol (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (e : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ e) = e := by
  induction e using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x => simp [sigR, hσ]

theorem cT_adMat (σ : E →ₐ[F] E) {a b : Type} (X : Matrix a b E) :
    cT (sigR (AF F) σ) (adMat F X) = adMat F (cT (σ : E →+* E) X) := by
  ext i k; simp [cT, adMat, sigR, inclR]

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

section Ring

variable {S : Type} [CommRing S] (s : S →+* S)

theorem images_ring {n j m : ℕ} (Ja Jai : Matrix (Fin n) (Fin n) S) (j0 k0 : Matrix (Fin m) (Fin m) S)
    (hJi : Jai * Ja = 1) (hk0 : k0 * j0 = 1)
    (c d C' D' : Matrix (Fin n) (Fin j) S) (z Z' : Matrix (Fin n) (Fin m) S)
    (cc : cT s c * Ja * c = 0) (dd : cT s d * Ja * d = 0) (cd : cT s c * Ja * d = 1) (dc : cT s d * Ja * c = 1)
    (cz : cT s c * Ja * z = 0) (dz : cT s d * Ja * z = 0) (zc : cT s z * Ja * c = 0) (zd : cT s z * Ja * d = 0)
    (zz : cT s z * Ja * z = j0)
    (sum : c * (cT s d * Ja) + z * (k0 * (cT s z * Ja)) + d * (cT s c * Ja) = 1)
    (cc' : cT s C' * Ja * C' = 0) (dd' : cT s D' * Ja * D' = 0) (cd' : cT s C' * Ja * D' = 1) (dc' : cT s D' * Ja * C' = 1)
    (cz' : cT s C' * Ja * Z' = 0) (dz' : cT s D' * Ja * Z' = 0) (zc' : cT s Z' * Ja * C' = 0) (zd' : cT s Z' * Ja * D' = 0)
    (zz' : cT s Z' * Ja * Z' = j0) :
    ∃ u : GL (Fin n) S, cT s u.1 * Ja * u.1 = Ja ∧ u.1 * c = C' ∧ u.1 * z = Z' ∧ u.1 * d = D' := by
  obtain ⟨pX, hpX⟩ : ∃ p, p = cT s d * Ja := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p, p = k0 * (cT s z * Ja) := ⟨_, rfl⟩
  obtain ⟨pY, hpY⟩ : ∃ p, p = cT s c * Ja := ⟨_, rfl⟩
  rw [← hpX, ← hp0, ← hpY] at sum
  have Xc : pX * c = 1 := by rw [hpX, dc]
  have Xz : pX * z = 0 := by rw [hpX, dz]
  have Xd : pX * d = 0 := by rw [hpX, dd]
  have Yc : pY * c = 0 := by rw [hpY, cc]
  have Yz : pY * z = 0 := by rw [hpY, cz]
  have Yd : pY * d = 1 := by rw [hpY, cd]
  have Oc : p0 * c = 0 := by rw [hp0, Matrix.mul_assoc, zc, Matrix.mul_zero]
  have Oz : p0 * z = 1 := by rw [hp0, Matrix.mul_assoc, zz, hk0]
  have Od : p0 * d = 0 := by rw [hp0, Matrix.mul_assoc, zd, Matrix.mul_zero]
  obtain ⟨g, hg⟩ : ∃ g, g = C' * pX + Z' * p0 + D' * pY := ⟨_, rfl⟩
  have gram : cT s g * Ja * g = Ja := by
    rw [hg, gram_comb s Ja j0 C' D' Z' pX pY p0 cc' dd' cd' dc' cz' dz' zc' zd' zz',
      ← gram_comb s Ja j0 c d z pX pY p0 cc dd cd dc cz dz zc zd zz, sum, cT_one, Matrix.one_mul, Matrix.mul_one]
  have hl : (Jai * cT s g * Ja) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g), gram, hJi]
  have hr : g * (Jai * cT s g * Ja) = 1 := mul_eq_one_comm.1 hl
  refine ⟨⟨g, Jai * cT s g * Ja, hr, hl⟩, gram, ?_, ?_, ?_⟩
  · change g * c = C'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xc, Oc, Yc, Matrix.mul_zero, Matrix.mul_one, add_zero]
  · change g * z = Z'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xz, Oz, Yz, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]
  · change g * d = D'
    simp only [hg, Matrix.add_mul, Matrix.mul_assoc, Xd, Od, Yd, Matrix.mul_zero, Matrix.mul_one, add_zero, zero_add]

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adMat_gram (σ : E →ₐ[F] E) {n a b : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin a) E)
    (Y : Matrix (Fin n) (Fin b) E) (R : Matrix (Fin a) (Fin b) E) (h : cT (σ : E →+* E) X * J * Y = R) :
    cT (sigR (AF F) σ) (adMat F X) * adMat F J * adMat F Y = adMat F R := by
  rw [cT_adMat, adMat, adMat, adMat, adMat, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem adMat_zero' {a b : Type} : adMat F (0 : Matrix a b E) = 0 := Matrix.map_zero _ (map_zero _)

theorem adMat_one' {a : Type} [DecidableEq a] : adMat F (1 : Matrix a a E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    adMat F (X * Y) = adMat F X * adMat F Y := Matrix.map_mul

end GlobalTheory.SphEis.ColImg

namespace GlobalTheory.SphEis.ColImg

open Formalism.UG (cT_mul cT_one)

theorem exists_point_images :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ (C' D' : Matrix (Fin n) (Fin j) (AF F ⊗[F] E)) (Z' : Matrix (Fin n) (Fin m) (AF F ⊗[F] E)), cT (sigR (AF F) σ) C' * adMat F J * C' = 0 → cT (sigR (AF F) σ) D' * adMat F J * D' = 0 → cT (sigR (AF F) σ) C' * adMat F J * D' = 1 → cT (sigR (AF F) σ) C' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) D' * adMat F J * Z' = 0 → cT (sigR (AF F) σ) Z' * adMat F J * Z' = adMat F J₀ → ∃ g : GAd σ J, (matHom _ σ J g).1 * adMat F C = C' ∧ (matHom _ σ J g).1 * adMat F Z = Z' ∧ (matHom _ σ J g).1 * adMat F D = D' := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr C' D' Z' cc dd cd cz dz zz
  have hσ : ∀ x, σ (σ x) = x := sig_invol fr.cm
  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := sigR_invol σ hσ
  have hJ : cT (sigR (AF F) σ) (adMat F J) = adMat F J := by rw [cT_adMat, cT_form fr.herm]
  have dc : cT (sigR (AF F) σ) D' * adMat F J * C' = 1 := by
    rw [← cT_gram _ hs _ hJ, cd, cT_one]
  have zc : cT (sigR (AF F) σ) Z' * adMat F J * C' = 0 := by rw [← cT_gram _ hs _ hJ, cz, cT_zero']
  have zd : cT (sigR (AF F) σ) Z' * adMat F J * D' = 0 := by rw [← cT_gram _ hs _ hJ, dz, cT_zero']
  have acc := adMat_gram (F := F) σ J C C 0 fr.cc
  have add := adMat_gram (F := F) σ J D D 0 fr.dd
  have acd := adMat_gram (F := F) σ J C D 1 fr.cd
  have adc := adMat_gram (F := F) σ J D C 1 fr.dc
  have acz := adMat_gram (F := F) σ J C Z 0 fr.cz
  have adz := adMat_gram (F := F) σ J D Z 0 fr.dz
  have azc := adMat_gram (F := F) σ J Z C 0 fr.zc
  have azd := adMat_gram (F := F) σ J Z D 0 fr.zd
  have azz := adMat_gram (F := F) σ J Z Z J₀ fr.zz
  rw [adMat_zero'] at acc add acz adz azc azd
  rw [adMat_one'] at acd adc
  have hJ0 : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm₀), adMat_one']
  have hJi : adMat F J⁻¹ * adMat F J = 1 := by
    rw [← adMat_mul', Matrix.nonsing_inv_mul _ (det_isUnit fr.herm), adMat_one']
  have hsum : adMat F C * (cT (sigR (AF F) σ) (adMat F D) * adMat F J) +
      adMat F Z * (adMat F J₀⁻¹ * (cT (sigR (AF F) σ) (adMat F Z) * adMat F J)) +
      adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) = 1 := by
    have := congrArg (adMat F) fr.sum
    rw [adMat_one'] at this
    rw [← this, cT_adMat, cT_adMat, cT_adMat]
    simp only [adMat_mul', adMat, Matrix.map_add _ (map_add _)]
  obtain ⟨u, hu, h1, h2, h3⟩ := images_ring (sigR (AF F) σ) (adMat F J) (adMat F J⁻¹) (adMat F J₀) (adMat F J₀⁻¹) hJi hJ0
    (adMat F C) (adMat F D) C' D' (adMat F Z) Z' acc add acd adc acz adz azc azd azz hsum cc dd cd dc cz dz zc zd zz
  exact ⟨(show HA (AF F) σ J from (⟨u, hu⟩ : HR (AF F) σ J)), h1, h2, h3⟩

end GlobalTheory.SphEis.ColImg
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem exists_isCompact_of_crd_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun p =>
    adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)
  have key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c) := by
    intro u b c h
    have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
        adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
      have := congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum
      simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
    calc (matHom _ σ J u).1 = (matHom _ σ J u).1 * 1 := (Matrix.mul_one _).symm
      _ = Φ (b, c) := by
        rw [← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z),
          ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]
  have hsig := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1 := continuous_fst
    have h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2 := continuous_snd
    have hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1 :=
      continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose
    exact ((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))
  have hadj : Continuous (adjA σ J) := by
    have : Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X :=
      (continuous_id.matrix_map hsig).matrix_transpose
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  let S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)
  let ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))
  have hψ : Continuous ψ := hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))
  have hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)
  refine ⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩
  intro u b c h hb hc
  refine ⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩
  have e1 := key u b c h
  have e2 := adjA_mat hFr.herm u
  simp only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]

end GlobalTheory.SphEis
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal


theorem _root_.GlobalTheory.T.archimedean_intertwiner_unique : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ),
    (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) →
    ∀ (T : SInf F κ →L[ℂ] SInf F κ)
      (A : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
        (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ w (f g : SInf F κ), (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
        (T g : (κ → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (T f)) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (κ → mixedEmbedding.mixedSpace F) (borel _),
        @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F κ,
          @integral _ ℂ _ _ (borel _) μ (fun x => T f x * starRingEnd ℂ (T f' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
  first | exact @GlobalTheory.ArchInvForm.const_of_intertwines | exact GlobalTheory.ArchInvForm.const_of_intertwines | (intros; apply GlobalTheory.ArchInvForm.const_of_intertwines <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_series_factorizable_restriction_finite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ i w, w ∉ S → φ' i w = G.M'.vac w) →
    (∀ u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
      ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
            (∑ i, pure (f' i) (φ' i)) x * starRingEnd ℂ (G.M'.co.rho B.ψ u (∑ i, pure (f' i) (φ' i)) x)) =
          @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => pure f φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (pure f φ) x)) →
    ∃ c : ℂ, ∑ i, pure (f' i) (φ' i) = c • pure f φ := by
  first | exact @GlobalTheory.SplitSvN.scalar_of_coeff | exact GlobalTheory.SplitSvN.scalar_of_coeff | (intros; apply GlobalTheory.SplitSvN.scalar_of_coeff <;> assumption)
end

section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.unitary_operator_commutes_schrodinger : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  first | exact @GlobalTheory.AdelicSchur.schur | exact GlobalTheory.AdelicSchur.schur | (intros; apply GlobalTheory.AdelicSchur.schur <;> assumption)
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch GlobalTheory.ResidueEisenstein
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.wittDecomposition_isotropicFrameEisenstein_dictionary : ∀ (D : D7) (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ (r + 1)), IsAniso V₀ → ∀ l : Lvl V, l.Good → HasIw d l.K → DataJ D.sp.cm.sig V.gram d.e d.e' l.L l.c (fun g => (iwAbs (absDet d) l.K g : ℝ)) ∧ (∃ T, IsRepsJ D.sp.cm.sig V.gram d.e T) ∧ ∀ T, IsRepsJ D.sp.cm.sig V.gram d.e T → ∀ (g : GA D V) (s : ℂ), sphericalEisensteinSeriesOnGroup d l.K g s = ∑' t : T, (((iwAbs (absDet d) l.K (t.1.1 * g) : ℝ≥0) : ℝ) : ℂ) ^ (s + ((V.rank : ℂ) - (r + 1)) / 2) := by
  first | exact @GlobalTheory.ResidueDictionary.dict | exact GlobalTheory.ResidueDictionary.dict | (intros; apply GlobalTheory.ResidueDictionary.dict <;> assumption)
end

section

open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

theorem _root_.GlobalTheory.T.flatSection_valuation_at_finitePlace_eq_sub_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ w, s.rho_vw w = (vAdd w b : ℝ) - (vAdd w (P.B w τ.1).det : ℝ) := by
  first | exact @GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | exact GlobalTheory.DefPt.rho_vw_eq_vAdd_sub | (intros; apply GlobalTheory.DefPt.rho_vw_eq_vAdd_sub <;> assumption)
end

section

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
open AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FreeLev

@[instance_reducible] def ptModule {E : Type} [Field E] [NumberField E] (P : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (act : OAct (𝓞 E) P.A) :
    letI := P.isAb.comm
    Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) :=
  letI := P.isAb.comm
  have h0 : act.act 0 = 1 := by
    have h := act.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  { smul := fun c q => Additive.ofMul (q.toMul ≫ act.act c)
    one_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 1) = q
      rw [act.one, Category.comp_id]; rfl
    mul_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a * b)) = Additive.ofMul ((q.toMul ≫ act.act b) ≫ act.act a)
      rw [mul_comm, act.mul, Category.assoc]
    smul_zero := fun c => by
      haveI := act.hom c
      show Additive.ofMul ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) ≫ act.act c) = Additive.ofMul 1
      rw [MonObj.one_comp]
    smul_add := fun c q q' => by
      haveI := act.hom c
      show Additive.ofMul ((q.toMul * q'.toMul) ≫ act.act c) = Additive.ofMul (q.toMul ≫ act.act c * q'.toMul ≫ act.act c)
      rw [MonObj.mul_comp]
    add_smul := fun a b q => by
      show Additive.ofMul (q.toMul ≫ act.act (a + b)) = Additive.ofMul (q.toMul ≫ act.act a * q.toMul ≫ act.act b)
      rw [act.add, MonObj.comp_mul]
    zero_smul := fun q => by
      show Additive.ofMul (q.toMul ≫ act.act 0) = Additive.ofMul 1
      rw [h0, MonObj.comp_one] }



theorem free_of_unip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (G : Type) [Group G] (h : G → (Dw.La →ₗ[𝓞 E] Dw.La)) (m g₁ g₂ : ℕ) (I₁ I₂ : Ideal (𝓞 E)), 1 ≤ Dw.p + Dw.q → g₁.Prime → g₂.Prime → g₁ ≠ g₂ → I₁ ≠ ⊤ → I₂ ≠ ⊤ → (g₁ : 𝓞 E) ∈ I₁ → (g₂ : 𝓞 E) ∈ I₂ → l.Mb ≤ I₁ → l.Mb ≤ I₂ → (∀ g x, ((h g - 1) ^ m) x ∈ I₁ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g x, ((h g - 1) ^ m) x ∈ I₂ • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ g, (∀ x, h g x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → g = 1) → FreePt Xo c (fun g => (h g, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La))) := by
  intro E _ _ _ H Dw l Xo c G _ h m g₁ g₂ I₁ I₂ _ hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ hu₁ hu₂ hfaith
  intro g k _ _ y y' hR hx
  obtain ⟨ρ, ν, -, hlev, hmove⟩ := hR
  have hfix : y.x ≫ ρ = y.x := hmove.1.symm.trans hx
  obtain ⟨x', hx'⟩ := GlobalTheory.T.exists_fixed_complexPoint_of_fixed_fieldPoint E H Dw l Xo k y.x ρ hfix
  obtain ⟨P, act, θ, N, ev, hθ, hN, hθN, hcomm, hadd, hlin, hker, honto, hrel⟩ :=
    GlobalTheory.T.exists_finiteOrder_fibreAut_at_levelMove_fixedPoint E H Dw l Xo x' ρ ν (h g) LinearMap.id hlev hx'
  have hM0 : 0 < l.M := by have := l.three_le; omega
  obtain ⟨Λ, _, _, F, ψ, hfin, htf, hFN, hψadd, hψlin, hψker, hψonto, hψF⟩ :=
    GlobalTheory.T.periodLattice_action_of_finiteOrder_automorphism E P act θ N l.M hθ hN hθN hcomm hM0
  letI := P.isAb.comm
  letI : Module (𝓞 E) (Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) := ptModule P act
  let evL : Dw.La →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ev a)
      map_add' := fun a b => congrArg Additive.ofMul (hadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hlin c a) }
  let ψL : Λ →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun a => Additive.ofMul (ψ a)
      map_add' := fun a b => congrArg Additive.ofMul (hψadd a b)
      map_smul' := fun c a => congrArg Additive.ofMul (hψlin c a) }
  let θL : Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) →ₗ[𝓞 E] Additive (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { toFun := fun q => Additive.ofMul (q.toMul ≫ θ)
      map_add' := fun q q' => by
        show Additive.ofMul ((q.toMul * q'.toMul) ≫ θ) = Additive.ofMul (q.toMul ≫ θ * q'.toMul ≫ θ)
        rw [MonObj.mul_comp]
      map_smul' := fun c q => by
        show Additive.ofMul ((q.toMul ≫ act.act c) ≫ θ) = Additive.ofMul ((q.toMul ≫ θ) ≫ act.act c)
        rw [Category.assoc, Category.assoc, hcomm] }
  have hMmem : (l.M : 𝓞 E) ∈ l.Mb := by
    have h1 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact Ideal.mul_le_left h1
  refine hfaith g (GlobalTheory.T.sub_mem_smul_top_of_neat_level_alt E Dw.La Λ _ l.Mb l.M N m g₁ g₂ I₁ I₂ evL ψL θL F (h g) hfin htf hM0 hMmem
    (fun a => by
      show Additive.ofMul (ev a) = 0 ↔ _
      rw [← hker a]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨a, ha⟩ := honto q.toMul (fun c hc => by
        have := hq c hc
        exact congrArg Additive.toMul this)
      exact ⟨a, congrArg Additive.ofMul ha⟩)
    (fun b => by
      show Additive.ofMul (ψ b) = 0 ↔ _
      rw [← hψker b]; exact ofMul_eq_zero)
    (fun q hq => by
      obtain ⟨b, hb⟩ := hψonto q.toMul (by
        have := congrArg Additive.toMul hq
        rwa [toMul_nsmul] at this)
      exact ⟨b, congrArg Additive.ofMul hb⟩)
    (fun b => congrArg Additive.ofMul (hψF b))
    (fun a => congrArg Additive.ofMul (hrel a))
    hN hFN hg₁ hg₂ hne hI₁ hI₂ hm₁ hm₂ hMb₁ hMb₂ (hu₁ g) (hu₂ g))

end GlobalTheory.FreeLev
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal


theorem _root_.GlobalTheory.T.exists_addChar_normalizing_schrodinger_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl (F := F)) [Invertible (2 : Fv F v)], ∃ ψv : AddChar (Fv F v) ℂ, Continuous ψv ∧ ψv ≠ 1 ∧
        ∃ A : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v),
          ∀ w, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr ψv w φ) = schr ψv (A w) (ev v φ) := by
  first | exact @GlobalTheory.ThK.ModelLocInt.exists_loc_schr | exact GlobalTheory.ThK.ModelLocInt.exists_loc_schr | (intros; apply GlobalTheory.ThK.ModelLocInt.exists_loc_schr <;> assumption)
end
