module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.exists_orthogonalComplement_embedding_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  first | exact @GlobalTheory.exists_orthCompl_hypPair | exact GlobalTheory.exists_orthCompl_hypPair | (intros; apply GlobalTheory.exists_orthCompl_hypPair <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.exists_cartanInvolution_extend_swapping_hyperbolicPair : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  first | exact @GlobalTheory.CartanPlane.extend_swap | exact GlobalTheory.CartanPlane.extend_swap | (intros; apply GlobalTheory.CartanPlane.extend_swap <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU


theorem _root_.GlobalTheory.T.exists_cartanInvolution_of_hasHermitianSignature : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ := by
  first | exact @GlobalTheory.CartanEx.exists_isCartan | exact GlobalTheory.CartanEx.exists_isCartan | (intros; apply GlobalTheory.CartanEx.exists_isCartan <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_linear_operator_l2_isometry : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.PolarSB.pairing_eq | exact GlobalTheory.PolarSB.pairing_eq | (intros; apply GlobalTheory.PolarSB.pairing_eq <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  first | exact @GlobalTheory.selfDual_pair_nondeg | exact GlobalTheory.selfDual_pair_nondeg | (intros; apply GlobalTheory.selfDual_pair_nondeg <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.supported_adelic_unitary_point_of_local_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl (F := F)) (n : ℕ) (X : Spc F E n) (L : Type) [Field L]
    (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) →
      ∀ (g : UA σ X.J) (A : Matrix (Fin n) (Fin n) L),
        mat g = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) + A.map ι → g ∈ UAt σ X (evFin F v) := by
  first | exact @GlobalTheory.InertLocFrame.uAt_of_local | exact GlobalTheory.InertLocFrame.uAt_of_local | (intros; apply GlobalTheory.InertLocFrame.uAt_of_local <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitary_adelic_place_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J), ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
    ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  first | exact @GlobalTheory.UnitaryPlaceSplit.exists_split_at | exact GlobalTheory.UnitaryPlaceSplit.exists_split_at | (intros; apply GlobalTheory.UnitaryPlaceSplit.exists_split_at <;> assumption)
end

section

open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew.CartanInv

theorem exists_isCartan : ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ), HasSig M r s → ∃ θ, IsCartan M θ :=
  GlobalTheory.CartanEx.exists_isCartan

end GlobalTheory.PlaneSkew.CartanInv
end

section

noncomputable section

open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SchrodTheta

variable {F : Type} [Field F] [NumberField F]

def HasTheta {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (f : W → ℂ) : Prop :=
  ∀ x, HasSum (fun ξ : κ → F => co.rho ψ x Φ fun i => algebraMap F (AF F) (ξ i)) (f x)

def IsPureSum {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (φ₀ : (κ → Fv F v₁) → ℂ) (Φ : (κ → AF F) → ℂ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
    Φ = ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ k, ∀ᶠ v in cofinite, φ k v = vac v) ∧
      ∀ k, φ k v₁ = φ₀

theorem isPureSum_zero {κ : Type} [Fintype κ] (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ)
    (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Fv F v₁) → ℂ) : IsPureSum vac v₁ φ₀ 0 :=
  ⟨0, Fin.elim0, Fin.elim0, by simp, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩

theorem IsPureSum.smul {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ) (c : ℂ) :
    IsPureSum vac v₁ φ₀ (c • Φ) := by
  obtain ⟨m, f, φ, rfl, h1, h2, h3⟩ := h
  refine ⟨m, fun k => c • f k, φ, ?_, h1, h2, h3⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  ring

theorem IsPureSum.add {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {Φ Ψ : (κ → AF F) → ℂ} (h : IsPureSum vac v₁ φ₀ Φ)
    (h' : IsPureSum vac v₁ φ₀ Ψ) : IsPureSum vac v₁ φ₀ (Φ + Ψ) := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaThird.main
  | exact _root_.GlobalTheory.ClosingLemmaThird.main
  | (apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaThird.main ..)

theorem IsPureSum.sum {κ : Type} [Fintype κ] {vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ}
    {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Fv F v₁) → ℂ} {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ k ∈ s, IsPureSum vac v₁ φ₀ (Φ k)) : IsPureSum vac v₁ φ₀ (∑ k ∈ s, Φ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPureSum_zero vac v₁ φ₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

section Theta

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
  (co : Darboux B κ) (ψ : AddChar (AF F) ℂ)

theorem rho_smul (x : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : co.rho ψ x (c • Φ) = c • co.rho ψ x Φ := by
  funext y
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem hasTheta_zero : HasTheta co ψ 0 0 := fun x => by
  have : co.rho ψ x 0 = 0 := by simpa using rho_smul co ψ x 0 0
  simpa [this] using (hasSum_zero : HasSum (fun _ : κ → F => (0 : ℂ)) 0)

variable {co ψ}

theorem HasTheta.smul {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (c : ℂ) :
    HasTheta co ψ (c • Φ) (c • f) := fun x => by
  rw [rho_smul]
  exact (h x).mul_left c

theorem HasTheta.add {Φ Ψ : (κ → AF F) → ℂ} {f g : W → ℂ} (h : HasTheta co ψ Φ f) (h' : HasTheta co ψ Ψ g) :
    HasTheta co ψ (Φ + Ψ) (f + g) := by
  intro x
  have h0 := (h x).add (h' x)
  simpa only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, mul_add] using h0

theorem HasTheta.sum {ι : Type} (s : Finset ι) {Φ : ι → (κ → AF F) → ℂ} {f : ι → W → ℂ}
    (h : ∀ k ∈ s, HasTheta co ψ (Φ k) (f k)) : HasTheta co ψ (∑ k ∈ s, Φ k) (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasTheta_zero co ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem HasTheta.thetaSum_eq {Φ : (κ → AF F) → ℂ} {f : W → ℂ} (h : HasTheta co ψ Φ f) (x : W) :
    thetaSum F (co.rho ψ x Φ) = f x :=
  (h x).tsum_eq

end Theta

end GlobalTheory.SchrodTheta

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.det_ne_zero_of_skewHermitianSelfDualLatticeSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  first | exact @GlobalTheory.SkewDet.det_ne_zero_of_isSkew | exact GlobalTheory.SkewDet.det_ne_zero_of_isSkew | (intros; apply GlobalTheory.SkewDet.det_ne_zero_of_isSkew <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem _root_.GlobalTheory.T.exists_isotropic_dual_partner_selfDual_hermitianLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  first | exact @GlobalTheory.TraceCorrection.exists_pair | exact GlobalTheory.TraceCorrection.exists_pair | (intros; apply GlobalTheory.TraceCorrection.exists_pair <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | exact GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | (intros; apply GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg <;> assumption)
end
