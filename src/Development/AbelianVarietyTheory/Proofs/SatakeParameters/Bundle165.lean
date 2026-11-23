module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle020
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle162
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.Emat

open Matrix

theorem gram_of_orth {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) (hCo : IsOrthCo σ J co) :
    star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J := by
  ext i k
  have h := hCo (Pi.single i 1) (Pi.single k 1)
  rw [Matrix.mul_apply]
  have hl : ∀ a, (star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)))) i a * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) a k =
      σ (co (Pi.single i 1) a) * co (Pi.single k 1) a := by
    intro a
    rw [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, hσ]
    rfl
  rw [Finset.sum_congr rfl fun a _ => hl a, h]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [Pi.single_apply, hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem toMatrix_toLE {E : Type} [Field E] {N : ℕ} (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((toLE γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = γ := by
  ext i j
  simp [toLE, LinearMap.toMatrix'_apply, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem unit_mat' {n N : ℕ} (hk : n = N) {E' : Type} [Field E'] [StarRing E'] (co coi γ J : Matrix (Fin N) (Fin N) E')
    (h1 : star co * co = J) (h2 : star γ * J * γ = J) (h3 : co * coi = 1) :
    (co * γ * coi).submatrix (finCongr hk) (finCongr hk) * star ((co * γ * coi).submatrix (finCongr hk) (finCongr hk)) = 1 := by
  subst hk
  have e2 : ∀ A : Matrix (Fin n) (Fin n) E', A.submatrix (finCongr rfl) (finCongr rfl) = A := fun A => by ext x y; rfl
  rw [e2, mul_eq_one_comm]
  calc star (co * γ * coi) * (co * γ * coi) = star coi * (star γ * (star co * co) * γ) * coi := by
        simp only [star_mul, Matrix.mul_assoc]
    _ = star coi * (star co * co) * coi := by rw [h1, h2]
    _ = star (co * coi) * (co * coi) := by simp only [star_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h3, star_one, Matrix.one_mul]

theorem star_eq_cT {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    star M = cT σ M := by
  ext i k
  simp [cT, Matrix.star_apply, hσ]

theorem orth_of_gram {E : Type} [Field E] (σ : E →+* E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hM : cT σ (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J) :
    IsOrthCo σ J co := by
  intro x y
  set M := LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) with hMdef
  have hx : ∀ z, co z = M *ᵥ z := fun z => by rw [hMdef, LinearMap.toMatrix'_mulVec]; rfl
  rw [← hM]

  simp only [hx, Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
  Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem toMatrix_stdG {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((stdG σ J γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) =
      LinearMap.toMatrix' ((stdCo σ J : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) * (γ : Matrix (Fin N) (Fin N) E) *
        LinearMap.toMatrix' (((stdCo σ J).symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) := by
  rw [← toMatrix_toLE γ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  rfl

theorem toMatrix_co_mul_symm {E : Type} [Field E] {N : ℕ} (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) * LinearMap.toMatrix' ((co.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

end GlobalTheory.TwV.Xc.Emat

end


open GlobalTheory.TwV.Xc.Emat in
theorem GlobalTheory.TwV.Xc.eMat_unitary_det : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (σ : E →+* E), (∀ x, σ x = star x) → ∀ (a N : ℕ) (hr : a = N) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E), cT σ crd.1 * crd.1 = J → IsOrthCo σ J (stdCo σ J) ∧ ∀ g ∈ UJ σ J, eMat hr σ J g * star (eMat hr σ J g) = 1 ∧ (eMat hr σ J g).det = g.1.det := by
  intro E _ _ _ σ hσ a N hr J crd hcrd
  subst hr
  have hco : IsOrthCo σ J (stdCo σ J) := by
    refine Classical.epsilon_spec (p := IsOrthCo σ J) ⟨toLE crd, ?_⟩
    refine orth_of_gram σ J _ ?_
    rw [toMatrix_toLE]
    exact hcrd
  refine ⟨hco, fun g hg => ?_⟩
  have hg' : star (g : Matrix (Fin a) (Fin a) E) * J * (g : Matrix (Fin a) (Fin a) E) = J := by
    rw [star_eq_cT σ hσ]
    exact hg
  unfold eMat
  rw [toMatrix_stdG]
  refine ⟨unit_mat' rfl _ _ _ J (gram_of_orth σ hσ J _ hco) hg' (toMatrix_co_mul_symm _), ?_⟩
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, toMatrix_co_mul_symm,
    Matrix.det_one, one_mul]
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc

theorem sameOff_of_isPt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n p : ℕ) (G : GAtP p) (A : LocAt F E n G) (J : Matrix (Fin n) (Fin n) E) :
    LocGood σ J A → ∀ (i : G.comp) (g g' : (∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)), A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∀ v, (∀ v', v' ≠ v → g v' = g' v') → SameOff (A.pl v).1 x.1 x'.1 := by
  intro H i g g' x x' hx hx' v hg w hw
  by_cases hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl A w hp
    have hv : v' ≠ v := fun h => hw (h ▸ rfl)
    have h1 := hx.2 v'
    have h2 := hx'.2 v'
    rw [hg v' hv] at h1
    have hmem : bc (prV (E := E) (A.pl v').1) ((x.1)⁻¹ * x'.1) ∈ UPts σ J ((A.pl v').1.adicCompletion F) :=
      Formalism.UG.P.afsplit_bc_mem σ J (A.pl v').1 _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ x.2) x'.2)
    have h3 := LocGood.eq_one_of_ph H v' _ hmem (by rw [map_mul, map_mul, map_inv, map_inv, h1, h2]; exact inv_mul_cancel _)
    rw [map_mul, map_inv] at h3
    exact (inv_mul_eq_one.1 h3)
  · rw [hx.1 w hp, hx'.1 w hp]

end GlobalTheory.TwV.Xc
end

section

open Matrix

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ringHomConjTranspose_mul_rev (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem sigmaConjTranspose_integral_gramSeparation (σ : L →+* L) (hv : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  show Valued.v (σ (A j i)) ≤ 1
  rw [hv]; exact hA j i

theorem val_div_pow_le_one {ϖ x y : L} {k m : ℕ} (hϖ : Valued.v ϖ ≤ 1) (hy : Valued.v y = Valued.v ϖ) (hϖ0 : ϖ ≠ 0)
    (hx : Valued.v x ≤ Valued.v ϖ ^ m) (hkm : k ≤ m) : x * (y ^ k)⁻¹ ∈ Formalism.UG.intL L := by
  show Valued.v (x * (y ^ k)⁻¹) ≤ 1
  have h0 : Valued.v ϖ ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)
  have h1 : Valued.v x ≤ Valued.v ϖ ^ k := hx.trans (pow_le_pow_right_of_le_one' hϖ hkm)
  rw [map_mul, map_inv₀, map_pow, hy]
  calc Valued.v x * (Valued.v ϖ ^ k)⁻¹ ≤ Valued.v ϖ ^ k * (Valued.v ϖ ^ k)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ h0

end GlobalTheory.Hk3.GramSep

namespace GlobalTheory.Hk3.GramSep

theorem eint : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ x, Valued.v (σ x) = Valued.v x) →
  ∀ (n r : ℕ) (JS a : GL (Fin n) L) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ) (Γ : Matrix (Fin r) (Fin r) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  (∀ k, 1 ≤ e k) → (∀ i k, M i k ∈ Formalism.UG.intL L) → (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) → Γ ∈ GlobalTheory.Hk3.GramSep.gam σ ϖ e →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L))) i j ∈ Formalism.UG.intL L) ∧ (∀ i j, ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) ∧
    ∀ i j, Valued.v ((M * Γ * Formalism.UG.cT σ M * (JS : Matrix (Fin n) (Fin n) L)) i j) < 1 := by
  intro L _ _ ϖ σ hvϖ hv n r JS a M e Γ hJS hSD he hM haM hΓ
  classical
  have hΓv : ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j) := hΓ.2
  have hϖlt : Valued.v ϖ < 1 := by
    rw [hvϖ, ← WithZero.coe_one, WithZero.coe_lt_coe]; decide
  have hϖ1 : Valued.v ϖ ≤ 1 := hϖlt.le
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  have hσϖ0 : σ ϖ ≠ 0 := (map_ne_zero σ).mpr hϖ0
  set ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hai
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJ
  set D : Matrix (Fin r) (Fin r) L := diagonal fun k => ϖ ^ e k with hD
  set Di : Matrix (Fin r) (Fin r) L := diagonal fun k => (ϖ ^ e k)⁻¹ with hDi
  set Ds : Matrix (Fin r) (Fin r) L := diagonal fun k => σ ϖ ^ e k with hDs
  set Dsi : Matrix (Fin r) (Fin r) L := diagonal fun k => (σ ϖ ^ e k)⁻¹ with hDsi
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
  have hDsiDs : Dsi * Ds = 1 := by
    rw [hDs, hDsi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext k; exact inv_mul_cancel₀ (pow_ne_zero _ hσϖ0)
  have hcTD : Formalism.UG.cT σ D = Ds := by
    rw [hD, hDs]; unfold Formalism.UG.cT
    rw [diagonal_map (map_zero σ), diagonal_transpose]
    congr 1; funext k; simp
  have haia : ai * A = 1 := by rw [hai, hA]; exact a.inv_mul
  have hcTa : Formalism.UG.cT σ ai * Formalism.UG.cT σ A = 1 := by
    have haai : A * ai = 1 := by rw [hai, hA]; exact a.mul_inv
    rw [← ringHomConjTranspose_mul_rev, haai]
    unfold Formalism.UG.cT; rw [Matrix.map_one σ (map_zero σ) (map_one σ), transpose_one]

  set P : Matrix (Fin n) (Fin r) L := ai * M * D with hP
  have hPi : ∀ i k, P i k ∈ Formalism.UG.intL L := by
    intro i k; rw [hP, hD, mul_diagonal]; exact haM i k
  set G1 : Matrix (Fin r) (Fin r) L := Di * Γ with hG1
  have hG1i : ∀ k j, G1 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG1, hDi, diagonal_mul, mul_comm]
    exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) (le_max_left _ _)
  set G2 : Matrix (Fin r) (Fin r) L := Γ * Dsi with hG2
  have hG2i : ∀ k j, G2 k j ∈ Formalism.UG.intL L := by
    intro k j; rw [hG2, hDsi, mul_diagonal]
    exact val_div_pow_le_one hϖ1 (hv ϖ) hϖ0 (hΓv k j) (le_max_right _ _)
  have hcTM := sigmaConjTranspose_integral_gramSeparation σ hv hM
  have hSDa : ∀ i j, (Formalism.UG.cT σ A * J * A) i j ∈ Formalism.UG.intL L := hSD.1
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · have e1 : ai * (M * Γ * Formalism.UG.cT σ M * J) = P * G1 * (Formalism.UG.cT σ M * J) := by
      rw [hP, hG1]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D Di, hDDi, Matrix.one_mul]
    rw [e1]
    exact matMul_int (matMul_int hPi hG1i) (matMul_int hcTM hJS) i j
  · have e2 : M * Γ * Formalism.UG.cT σ M * J * A = M * G2 * (Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A)) := by
      rw [hP, hG2, ringHomConjTranspose_mul_rev, ringHomConjTranspose_mul_rev, hcTD]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Dsi Ds, hDsiDs, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.cT σ ai) (Formalism.UG.cT σ A), hcTa,
        Matrix.one_mul]
    rw [e2]
    exact matMul_int (matMul_int hM hG2i) (matMul_int (sigmaConjTranspose_integral_gramSeparation σ hv hPi) hSDa) i j
  · set G3 : Matrix (Fin r) (Fin r) L := Matrix.of fun k j => Γ k j * (ϖ ^ 1)⁻¹ with hG3
    have hG3i : ∀ k j, G3 k j ∈ Formalism.UG.intL L := by
      intro k j
      exact val_div_pow_le_one hϖ1 rfl hϖ0 (hΓv k j) ((he k).trans (le_max_left _ _))
    have hΓ3 : Γ = ϖ • G3 := by
      ext k j; rw [hG3]; simp only [Matrix.smul_apply, of_apply, smul_eq_mul, pow_one]
      field_simp
    have e3 : M * Γ * Formalism.UG.cT σ M * J = ϖ • (M * G3 * Formalism.UG.cT σ M * J) := by
      rw [hΓ3, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    rw [e3, Matrix.smul_apply, smul_eq_mul, map_mul]
    have hint : Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ 1 :=
      matMul_int (matMul_int (matMul_int hM hG3i) hcTM) hJS i j
    calc Valued.v ϖ * Valued.v ((M * G3 * Formalism.UG.cT σ M * J) i j) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hϖlt

end GlobalTheory.Hk3.GramSep
end
end

section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem dualA_hform_eq {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem dualA_conj_mulVec {L : Type} [Field L] (σ : L →+* L) {a b : ℕ} (y : Matrix (Fin a) (Fin b) L) (w : Fin b → L) :
    (fun i => σ ((y *ᵥ w) i)) = (y.map σ) *ᵥ (fun i => σ (w i)) := by
  funext i

  simp [dotProduct, Matrix.mulVec, map_sum]

theorem dualA_mulVec_int {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {a b : ℕ}
    {A : Matrix (Fin a) (Fin b) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) {w : Fin b → L}
    (hw : ∀ i, w i ∈ Formalism.UG.intL L) (i : Fin a) : (A *ᵥ w) i ∈ Formalism.UG.intL L := by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hw k)

theorem hermDual_subset_of_gram_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS0 hT0 x hx v h1 h2
  have hS : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := HoweSwap.cT_herm hS0
  have hT : Formalism.UG.cT σ (JT : Matrix (Fin n') (Fin n') L) = JT := HoweSwap.cT_herm hT0
  have hSi := HoweSwap.cT_inv_herm JS hS
  obtain ⟨hS1, hS2⟩ := HoweSwap.glint_int hJS
  obtain ⟨hT1, hT2⟩ := HoweSwap.glint_int hJT
  have hint : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rwa [hv]
  obtain ⟨l, w, hl, hw, hz⟩ := GlobalTheory.T.dual_integral_preimage_le_sum_transpose_image L n' n (x.map σ) ((JS : Matrix (Fin n) (Fin n) L) *ᵥ v) (by
    intro u hu hxu
    have e : x *ᵥ (fun i => σ (u i)) = fun i => σ ((x.map σ *ᵥ u) i) := by
      rw [dualA_conj_mulVec]
      congr 1
      ext i j; simp [hσ]
    have := h1 (fun i => σ (u i)) (fun i => hint _ (hu i)) (fun i => by rw [e]; exact hint _ (hxu i))
    rw [dualA_hform_eq] at this
    simpa [dotProduct, hσ] using this)
  have hc : ∀ {a b : Type} (Z : Matrix a b L), (Z.map σ)ᵀ = Formalism.UG.cT σ Z := fun _ => rfl
  have hy : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    simp only [adj, Formalism.UG.cT_mul, HoweSwap.cT_cT hσ, hT, hSi, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hTxv : ∀ k, (((JT : Matrix (Fin n') (Fin n') L) * x) *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := h2 (Pi.single k 1) (fun i => by
      by_cases h : i = k
      · subst h; simp
      · simp [h])
    rw [dualA_hform_eq, dualA_conj_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc,
      Matrix.mulVec_mulVec, hy] at this
    have e : (fun i => σ ((Pi.single k 1 : Fin n' → L) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [h]
    rw [e] at this
    simpa using this
  have hxv : ∀ k, (x *ᵥ v) k ∈ Formalism.UG.intL L := by
    intro k
    have := dualA_mulVec_int hT2 hTxv k
    rwa [Matrix.mulVec_mulVec, HoweSwap.inv_mul_cl] at this
  have hyw : adj σ JS JT x *ᵥ (((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w) =
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [Matrix.mulVec_mulVec, adj, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, hc]
  have hv2 : v = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l +
      (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hz, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l,
    ((JT⁻¹ : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *ᵥ w, dualA_mulVec_int hS2 hl, fun i => ?_,
    dualA_mulVec_int hT2 hw, by rw [hyw]; exact hv2⟩
  have e : x *ᵥ (((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ l) = x *ᵥ v -
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (x.map σ)ᵀ) *ᵥ w := by
    conv_rhs => rw [hv2]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec w, ← Matrix.mul_assoc, add_sub_cancel_right]
  rw [e, Pi.sub_apply]
  exact Subring.sub_mem _ (hxv i) (dualA_mulVec_int hx hw i)

end GlobalTheory.Hk3.HoweG
end

section

open Matrix

namespace GlobalTheory.Hk3.HoweG.GramA

variable {L : Type} [Field L]

theorem hform_eq_dot (σ : L →+* L) {n : ℕ} (J : Matrix (Fin n) (Fin n) L) (a b : Fin n → L) :
    Formalism.UG.hform σ J a b = (fun i => σ (a i)) ⬝ᵥ (J *ᵥ b) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem map_mulVec_eq (σ : L →+* L) {n m : ℕ} (A : Matrix (Fin n) (Fin m) L) (w : Fin m → L) :
    (fun i => σ ((A *ᵥ w) i)) = (fun i => σ (w i)) ᵥ* Formalism.UG.cT σ A := by
  ext i

  simp [Formalism.UG.cT, dotProduct, Matrix.mulVec, Matrix.vecMul, map_sum, mul_comm]

theorem dot_mem (O : Subring L) {n : ℕ} {a b : Fin n → L} (ha : ∀ i, a i ∈ O) (hb : ∀ i, b i ∈ O) : a ⬝ᵥ b ∈ O :=
  Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ha k) (hb k)

theorem mulVec_mem (O : Subring L) {n m : ℕ} {A : Matrix (Fin n) (Fin m) L} {b : Fin m → L}
    (hA : ∀ i j, A i j ∈ O) (hb : ∀ i, b i ∈ O) : ∀ i, (A *ᵥ b) i ∈ O :=
  fun i => dot_mem O (hA i) hb

theorem hform_integral : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ (u u' : Fin n → L) (w w' : Fin n' → L), (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
      (∀ i, w i ∈ Formalism.UG.intL L) → (∀ i, u' i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u') i ∈ Formalism.UG.intL L) →
      (∀ i, w' i ∈ Formalism.UG.intL L) →
      Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w)
        (u' + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w') ∈ Formalism.UG.intL L := by
  intro L _ _ σ n n' JS JT hσ hv hJS hJT hS hT x hx u u' w w' hu hxu hw hu' hxu' hw'
  have hS' := HoweSwap.cT_herm hS
  have hT' := HoweSwap.cT_herm hT
  have hSi := HoweSwap.cT_inv_herm JS hS'
  have iS : ∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJS).1
  have iT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := (HoweSwap.glint_int hJT).1
  have hσO : ∀ z, z ∈ Formalism.UG.intL L → σ z ∈ Formalism.UG.intL L := by
    intro z hz
    simp only [Formalism.UG.intL, Valuation.mem_integer_iff] at hz ⊢
    rw [hv]; exact hz
  have e1 : (JS : Matrix (Fin n) (Fin n) L) * adj σ JS JT x = Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj
    rw [Matrix.mul_assoc, HoweSwap.mul_inv_cl]
  have e2 : Formalism.UG.cT σ (adj σ JS JT x) * (JS : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n') (Fin n') L) * x := by
    unfold adj
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hT', hSi, HoweSwap.cT_cT hσ, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul,
      Matrix.mul_one]
  have e3 : x * adj σ JS JT x = (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *
      (JT : Matrix (Fin n') (Fin n') L) := by
    unfold adj Formalism.UG.cT
    simp only [Matrix.mul_assoc]
  have h1 : ∀ b : Fin n → L, Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (u + adj σ JS JT x *ᵥ w) b =
      (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ b) +
        (fun i => σ (w i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ (x *ᵥ b)) := by
    intro b
    have : (fun i => σ ((u + adj σ JS JT x *ᵥ w) i)) = (fun i => σ (u i)) + fun i => σ ((adj σ JS JT x *ᵥ w) i) := by
      ext i; simp
    rw [hform_eq_dot, this, add_dotProduct, map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2,
      Matrix.mulVec_mulVec]
  have h2 : (fun i => σ (u i)) ⬝ᵥ ((JS : Matrix (Fin n) (Fin n) L) *ᵥ (adj σ JS JT x *ᵥ w')) =
      (fun i => σ ((x *ᵥ u) i)) ⬝ᵥ ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [map_mulVec_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e1]
  have h3 : x *ᵥ (adj σ JS JT x *ᵥ w') =
      (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) *ᵥ
        ((JT : Matrix (Fin n') (Fin n') L) *ᵥ w') := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e3]
  rw [h1, Matrix.mulVec_add, dotProduct_add, h2, Matrix.mulVec_add, h3]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact dot_mem _ (fun i => hσO _ (hu i)) (mulVec_mem _ iS hu')
  · exact dot_mem _ (fun i => hσO _ (hxu i)) (mulVec_mem _ iT hw')
  · refine dot_mem _ (fun i => hσO _ (hw i)) (mulVec_mem _ iT fun i => ?_)
    exact add_mem (hxu' i) (mulVec_mem _ hx (mulVec_mem _ iT hw') i)

end GlobalTheory.Hk3.HoweG.GramA
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient : ∀ (K : Type) [Field K] (n q : ℕ) (a b : ℕ → K) (s s' : K), (q : K) ≠ 0 → s ≠ 0 → 0 < n → a 0 = 1 → (∀ j, j ≤ n → b j * a n = a (n - j)) → dualPoly (s * s' * (q : K) ^ (n - 1)) ((Formalism.L2.Col.heckePolyOf n q b).comp (C s * X)) = (Formalism.L2.Col.heckePolyOf n q a).comp (C s' * X) := by
  first | exact @GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | exact GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp | (intros; apply GlobalTheory.Hk3.DualHecke.dualPoly_heckePolyOf_comp <;> assumption)
end
