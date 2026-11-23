module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacUnique

open GlobalTheory.FockCompare

variable {D : D7}

def hAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace

def omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hAt S T τ x y).re

theorem omAt_add_left (S T : HSp D) (τ : D.what₂.Tau) (x x' y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (x + x') y = omAt S T τ x y + omAt S T τ x' y := by
  simp only [omAt, hAt, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem omAt_add_right (S T : HSp D) (τ : D.what₂.Tau) (x y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (y + y') = omAt S T τ x y + omAt S T τ x y' := by
  simp only [omAt, hAt, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

theorem omAt_smul_left (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (c • x) y = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

theorem omAt_smul_right (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (c • y) = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, omAt S T τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_left S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_left S T τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_right S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_right S T τ c _ _)

theorem omO_apply (S T : HSp D) (x y : RW T S) : omO S T x y = ∑ τ, omAt S T τ (x τ) (y τ) := rfl

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun x := fun τ => cplxO (sS τ) (sT τ) (x τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem jO_apply (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : RW T S) (τ : D.what₂.Tau) :
    jO S T sS sT x τ = cplxO (sS τ) (sT τ) (x τ) := rfl

def infRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S where
  toFun γ := fun τ i j => tauE D τ (γ i j)
  map_zero' := by funext τ i j; exact (tauE D τ).map_zero
  map_add' x y := by funext τ i j; exact (tauE D τ).map_add _ _

def finRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T where
  toFun γ := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (γ i j)
  map_zero' := by funext i j; exact TensorProduct.tmul_zero _ _
  map_add' x y := by funext i j; exact TensorProduct.tmul_add _ _ _

theorem finRat_inf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (infPart D) = 0 := by
  funext i j
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (γ i j) = 0
  exact TensorProduct.zero_tmul _ _

theorem finRat_fin (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (finPart D) = (ratW T S γ).map (finPart D) := rfl

theorem piW_of_inf (θ : InfFam D) {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) :
    piW θ T S u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero]

theorem piW_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : piW θ T S (ratW T S γ) = infRat S T γ := by
  funext τ i j
  exact comp_incA hθ τ _

theorem ratW_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S γ = iotaW σ T S (infRat S T γ) + finRat S T γ := by
  have e : (ratW T S γ - finRat S T γ : WA T S) = iotaW σ T S (infRat S T γ) := by
    refine h.real_ext ?_ (h.real_iota T S _) ?_
    · funext i j
      have e1 : finPart D (finRat S T γ i j) = finPart D (ratW T S γ i j) := rfl
      show finPart D (ratW T S γ i j - finRat S T γ i j) = 0
      rw [RingHom.map_sub, e1, sub_self]
    · rw [AddMonoidHom.map_sub, piW_of_inf θ (finRat_inf S T γ), piW_ratW h.inf, h.pi_iota, sub_zero]
  exact sub_eq_iff_eq_add.1 e

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    u.map (infPart D) = 0 := by
  have : latO S T LS LT P ≤ ((infPart D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    funext i j
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  exact this hu

end GlobalTheory.VacUnique

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LatVac
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatVacDual

theorem exists_extension {O E V : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
    (Λ : Submodule O V) (hspan : Submodule.span E (Λ : Set V) = ⊤) (φ : Λ →ₗ[O] O) :
    ∃ ψ : V →ₗ[E] E, ∀ x : Λ, ψ x = algebraMap O E (φ x) := by
  haveI : IsLocalizedModule (nonZeroDivisors O) Λ.subtype :=
    { map_units := fun x => by
        rw [Module.End.isUnit_iff]
        have hx : algebraMap O E x ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
        refine ⟨fun a b h => ?_, fun b => ⟨(algebraMap O E x)⁻¹ • b, ?_⟩⟩
        · have h' : algebraMap O E x • a = algebraMap O E x • b := by
            simpa [Module.algebraMap_end_apply] using h
          exact smul_right_injective V hx h'
        · rw [Module.algebraMap_end_apply, ← algebraMap_smul E, smul_smul, mul_inv_cancel₀ hx, one_smul]
      surj := fun y => by
        have hy : y ∈ Submodule.span E (Λ : Set V) := hspan ▸ Submodule.mem_top
        obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) E _ y hy
        rw [Submodule.span_eq] at ht
        exact ⟨(⟨_, ht⟩, t), rfl⟩
      exists_of_eq := fun {a b} h => ⟨1, by rw [Λ.injective_subtype h]⟩ }
  let g : V →ₗ[O] E := IsLocalizedModule.lift (nonZeroDivisors O) Λ.subtype
    ((Algebra.linearMap O E).comp φ) (IsLocalizedModule.map_units (Algebra.linearMap O E))
  refine ⟨g.extendScalarsOfIsLocalization (nonZeroDivisors O) E, fun x => ?_⟩
  exact IsLocalizedModule.lift_apply (nonZeroDivisors O) Λ.subtype ((Algebra.linearMap O E).comp φ)
    (IsLocalizedModule.map_units (Algebra.linearMap O E)) x

theorem exists_dual_family {E : Type} [Field E] [NumberField E] [StarRing E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (hG : ∀ i j, star (G i j) = G j i) (hdet : IsUnit G.det)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hsd : ∀ y : Fin r → E, (∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) → y ∈ Λ) :
    ∃ (n : ℕ) (s s' : Fin n → Fin r → E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧
      ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * G k j = if a = j then 1 else 0 := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property f LinearMap.id hf
  choose ψ hψ using fun i : Fin n => exists_extension Λ hspan ((LinearMap.proj i).comp σ)
  let c : Fin n → Fin r → E := fun i j => ψ i (Pi.single j 1)
  have hc : ∀ i x, ψ i x = ∑ j, x j * c i j := by
    intro i x
    conv_lhs => rw [pi_eq_sum_univ' x]

    simp [c, map_sum]
  let s' : Fin n → Fin r → E := fun i => star (c i ᵥ* G⁻¹)
  have hs' : ∀ i j, ∑ k, star (s' i k) * G k j = c i j := by
    intro i j
    have : (c i ᵥ* G⁻¹) ᵥ* G = c i := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    rw [← congrFun this j]
    simp [s', Matrix.vecMul, dotProduct]
  let s : Fin n → Fin r → E := fun i => f (Pi.single i 1)
  refine ⟨n, s, s', fun i => ⟨(f (Pi.single i 1)).2, hsd _ fun x hx => ?_⟩, fun a j => ?_⟩
  · have h1 : ∑ a, ∑ b, star (x a) * G a b * s' i b = star (ψ i x) := by
      rw [hc, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hs', star_mul', star_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', star_star, hG]; ring
    have h2 := hψ i ⟨x, hx⟩
    rw [h1]
    refine ⟨⟨star (ψ i x), ?_⟩, rfl⟩
    have h3 : IsIntegral ℤ (ψ i x) := by
      rw [show ψ i x = _ from h2]
      exact RingOfIntegers.isIntegral_coe _
    exact h3.map (starRingEnd E).toIntAlgHom
  · have key : (∑ i, (ψ i).smulRight (s i) : (Fin r → E) →ₗ[E] (Fin r → E)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun x hx => ?_
      have h1 : f (σ ⟨x, hx⟩) = ⟨x, hx⟩ := LinearMap.congr_fun hσ ⟨x, hx⟩

      rw [pi_eq_sum_univ' (σ ⟨x, hx⟩), map_sum] at h1
      have h2 := congrArg Λ.subtype h1

      rw [map_sum] at h2
      rw [LinearMap.sum_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [LinearMap.smulRight_apply, show ψ i x = _ from hψ i ⟨x, hx⟩, algebraMap_smul, map_smul, map_smul]
      rfl
    have h := congrFun (LinearMap.congr_fun key (Pi.single j 1)) a
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.id_apply, Pi.single_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hs', mul_comm]

theorem dualFamily : ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), IsSelfDualC S Λ → ∃ (n : ℕ) (s s' : Fin n → Fin S.rank → D.host.E), (∀ i, s i ∈ Λ ∧ s' i ∈ Λ) ∧ ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0 := by
  intro D S Λ h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) = ⊤ := by
    obtain ⟨t, ht⟩ := h.1.fg
    apply eq_top_iff.mpr
    intro y _
    let p : (Fin S.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * S.gram i j * y j
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) t p
    have hp : ∀ x ∈ Λ, IsIntegral ℤ ((b : 𝓞 D.host.E) • p x) := by
      intro x hx
      rw [← ht] at hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hb x hx
        rw [← ha]
        exact RingOfIntegers.isIntegral_coe a
      | zero => simpa [p] using (isIntegral_zero : IsIntegral ℤ (0 : D.host.E))
      | add x z hx hz ihx ihz =>
        have heq : p (x + z) = p x + p z := by
          simp [p, star_add, add_mul, Finset.sum_add_distrib]
        rw [heq, smul_add]
        exact ihx.add ihz
      | smul c x hx ih =>
        have heq : p (c • x) = star (c : D.host.E) * p x := by
          simp only [p, Pi.smul_apply, algebraMap_smul, star_mul', Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          change star ((c : D.host.E) * x i) * S.gram i j * y j = _
          rw [star_mul']
          ring
        rw [heq, Algebra.smul_def]
        have hc := (RingOfIntegers.isIntegral_coe c).map (starRingEnd D.host.E).toIntAlgHom
        have hc' : IsIntegral ℤ (star (c : D.host.E)) := hc
        convert hc'.mul ih using 1 <;> simp only [Algebra.smul_def] <;> ring
    have hy : (b : 𝓞 D.host.E) • y ∈ Λ := (h.2 _).2 (by
      intro x hx
      have hi := hp x hx
      refine ⟨⟨_, ?_⟩, rfl⟩
      have heq : (∑ i, ∑ j, star (x i) * S.gram i j * ((b : 𝓞 D.host.E) • y) j) =
          (b : 𝓞 D.host.E) • p x := by
        simp only [p, Pi.smul_apply, algebraMap_smul, Algebra.smul_def, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
      change IsIntegral ℤ (∑ i, ∑ j, star (x i) * S.gram i j * ((b : 𝓞 D.host.E) • y) j)
      rw [heq]
      exact hi)
    have hb0 : (algebraMap (𝓞 D.host.E) D.host.E b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    have hy' : (b : 𝓞 D.host.E) • y ∈ Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) :=
      Submodule.subset_span hy
    have hy'' : (algebraMap (𝓞 D.host.E) D.host.E b) • y ∈
        Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E)) := by
      simpa only [algebraMap_smul] using hy'
    have := (Submodule.span D.host.E (Λ : Set (Fin S.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E b)⁻¹ hy''
    rw [smul_smul, inv_mul_cancel₀ hb0, one_smul] at this
    exact this
  exact exists_dual_family S.gram (gram_star S) (gram_det_isUnit S) Λ h.1.fg hspan
    fun y hy => (h.2 y).2 hy

end GlobalTheory.LatVacDual
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory


open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow :
    ∀ (K : Type) [Field K] [NumberField K], Countable (Ideal (𝓞 K)) ∧ ∀ σ : ℝ, 1 < σ → (Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∧ Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  intro K _ _
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hU : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
      ext I; simp
    have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
      rw [hU]
      exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
    exact Set.countable_univ_iff.mp hc
  · have hsum : Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
      have h := _root_.GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
      refine h.congr fun I => ?_
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
      simp
    refine ⟨hsum, ?_⟩
    have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
      fun P Q h => HeightOneSpectrum.ext h
    exact hsum.comp_injective hinj

end GlobalTheory
end
