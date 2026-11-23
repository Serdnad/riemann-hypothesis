module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.UnitHermitianSpace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LinearFormAdelic
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle005
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle011
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle004

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def SDarb_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∃ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd ∧ ∀ x : Matrix (Fin m) (Fin n ⊕ Fin n) E, ∃ y z : Fin m × Fin n × Fin 2 → F,
      dd.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))
def SEv_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (bs : Module.Basis (Fin 2) F E) (m n : ℕ) (A : Spc F E m) (Y : Spc F E n)
  (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ m → 1 ≤ n →
  (A.IsHerm σ B r s ∧ (∀ i j, σ (Y.J j i) = -Y.J i j) ∨ A.IsSkew σ B r s ∧ ∀ i j, σ (Y.J j i) = Y.J i j) →
  IsFrame2 σ Y b → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε →
  ∀ dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2),
    IsAdapted bs A Y b dd →
    ev0 (F := F) (Fin m × Fin n × Fin 2) ∈ (adeleClass F).adm (Fin m × Fin n × Fin 2) ∧
    (∀ z : Matrix (Fin m) (Fin n) (AE F E), ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2),
      ev0 _ (dd.rho B.ψ (z * (diagCols (Fin n))ᵀ) Φ) = ev0 _ Φ) ∧
    ∀ Φ ∈ schA F (Fin m × Fin n × Fin 2), HasSum (fun y : Matrix (Fin m) (Fin n) E =>
      ev0 _ (dd.rho B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) (thetaSum F Φ)
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isHerm_unitSpc_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (n : ℕ) : (unitSpc F E n).IsHerm σ B n 0 := by
  refine ⟨fun i j => ?_, fun w => ?_, isLattice_stdLattice, fun y => ?_, fun w => ?_, fun v => ?_⟩
  · simp only [unitSpc, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · exact map_one σ
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact map_zero σ
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hasSig_one
  · simp only [unitSpc]
    rw [mem_std]
    constructor
    · intro hy x hx
      rw [mem_std] at hx
      rw [form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (map_isIntegral_int σ (hx i))
    · intro h i
      have hx : (Pi.single i (1 : E) : Fin n → E) ∈ stdLattice E n := by
        rw [mem_std]
        intro j
        by_cases e : j = i
        · subst e; simpa using isIntegral_one
        · simpa [Pi.single_apply, e] using isIntegral_zero
      have := h _ hx
      rw [form_one] at this
      simpa [Pi.single_apply] using this
  · simp only [unitSpc, Matrix.map_one _ (map_zero _) (map_one _)]
    exact isCartan_one
  · exact isSplitBasis_stdLattice (B.τ v) hB.cm
end PositivityTheory.SiegelWeilFormula.Ldexb.UnitHermitianSpace
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem sigma_invol'_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem exists_ne_sigma_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push Not at hne
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hB.cm.2.1.isComplex _
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  show NumberField.ComplexEmbedding.conjugate τ = τ
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  show star (τ x) = τ x
  rw [← hB.cm.2.2.2 τ x, hne x]
theorem fixed_mem_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {q : E} (hq : σ q = q) : ∃ f : F, algebraMap F E f = q := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent F ![(1 : E), q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      apply hne (-(s / t))
      have h1 : t • q = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : q = t⁻¹ • -(s • (1 : E)) := by rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hB.cm.2.2.1]; rfl
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hσid : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · simp
    · simpa using hq
  obtain ⟨x, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.exists_ne_sigma_k hB
  exact hx (by simpa using LinearMap.congr_fun hσid x)
theorem eig_line_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {k : ℤ} (hk : k * k = 1) {δ y : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) (hy : σ y = (k : E) * y) : ∃ f : F, y = f • δ := by
  have hk0 : (k : E) ≠ 0 := by
    intro h
    have h1 : ((k * k : ℤ) : E) = 1 := by rw [hk]; simp
    rw [Int.cast_mul, h, zero_mul] at h1
    exact zero_ne_one h1
  have hfix : σ (y / δ) = y / δ := by
    rw [map_div₀, hy, hδ, mul_div_mul_left _ _ hk0]
  obtain ⟨f, hf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.fixed_mem_k hB hfix
  refine ⟨f, ?_⟩
  rw [Algebra.smul_def, hf, div_mul_cancel₀ _ hδ0]
theorem eig_AE_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {k : ℤ} (hk : k * k = 1) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) {z : AE F E} (hz : cA σ z = (k : AE F E) * z) :
    z = linearFormAdelic (F := F) δ z • inclR (F := F) (AF F) δ := by
  have hinv := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.sigma_invol'_k hB
  set ℓ : E →ₗ[F] F := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hℓ : ℓ δ = 1 := ell_spec hδ0
  have hsm : ∀ x : E, (k : F) • x = (k : E) * x := fun x => by rw [Algebra.smul_def, map_intCast]
  have hkk : (k : F) * k = 1 := by exact_mod_cast hk
  let g : E →ₗ[F] E := ℓ.smulRight δ
  let p : E →ₗ[F] E := LinearMap.id + (k : F) • σ.toLinearMap
  have hzero : (LinearMap.id - g) ∘ₗ p = 0 := by
    ext e
    have hw : σ (e + (k : F) • σ e) = (k : E) * (e + (k : F) • σ e) := by
      rw [hsm (σ e), map_add (f := _), map_mul, map_intCast, hinv, mul_add, ← mul_assoc, ← Int.cast_mul, hk, Int.cast_one, one_mul,
        add_comm]
    obtain ⟨f, hf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Meas.eig_line_k hB hk hδ0 hδ hw
    show (e + (k : F) • σ e) - ℓ (e + (k : F) • σ e) • δ = 0
    rw [hf, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  have hbc : ∀ w : AE F E, (LinearMap.id - g).baseChange (AF F) w = w - linearFormAdelic (F := F) δ w • inclR (F := F) (AF F) δ := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [LinearMap.baseChange_tmul, inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [linearFormAdelic, g, LinearMap.baseChange_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), add_smul]
      abel
  have hpc : ∀ w : AE F E, p.baseChange (AF F) w = w + (k : F) • cA σ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [p, cA, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), smul_add]
      abel
  have hkz : (k : F) • cA σ z = z := by
    rw [hz, show ((k : ℤ) : AE F E) = algebraMap F (AE F E) (k : F) by rw [map_intCast], ← Algebra.smul_def, smul_smul, hkk,
      one_smul]
  have h2 : p.baseChange (AF F) z = (2 : F) • z := by
    rw [hpc, hkz, two_smul]
  have h0 : (LinearMap.id - g).baseChange (AF F) (p.baseChange (AF F) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [h2, LinearMap.map_smul_of_tower, hbc] at h0
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left two_ne_zero))
end PositivityTheory.SiegelWeilFormula.Act.C5.Meas
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def SWAnisoX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) r s r' s', _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → 1 ≤ d → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → min r' s' = 0 → M.IsGood B.ψ →
    ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ dd om S l, IsDblCoordX M dd → IsDbl (σ := σ) (A := W) (Y := X) B.ψ dd χ om S l →
    ∀ K a, IsStab2 B K → IsHgt K a →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ Φ₁ ∈ PolData B M, ∀ Φ₂ ∈ PolData B M,
      EisValueAt (flat a (fun x => l (om x (boxFun Φ₁ (star Φ₂)))) (((d : ℂ) - n) / 2)) (((d : ℂ) - n) / 2)
        fun x => (if n < d then 1 else 2) * ⨍ h in D, thetaSum F (om x (S h (boxFun Φ₁ (star Φ₂)))) ∂μ
end GlobalTheory.ThK.Dbl
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}
variable {Y : Spc F E n} {A : Spc F E m}
def HgtEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    (∃ K a, IsStab2 (σ := σ) (Y := Y) B K ∧ IsHgt K a ∧ Continuous a ∧ ∀ x, 0 < a x) ∧
    ∃ e : UA σ Y.J × UA σ Y.J →* G2 σ Y, Continuous e ∧ ∀ h h', IsEmb h h' (e (h, h'))
def Unfold0_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → min r s = 0 →
    ∀ (χ : Chr F E) (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsHecke F E χ → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ (f Ê : G2 σ Y → ℂ) (z : ℂ), Continuous f → Continuous Ê → (∀ x, HasSum (eisTerm f x) (Ê x)) →
      (∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x) →
    ∀ (μ : Measure (UA σ Y.J)) (D : Set (UA σ Y.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ Y.J) D μ →
      Integrable (fun g => f (e (1, g))) μ → ∀ φ : UA σ Y.J → ℂ, IsRapid φ → ∀ h,
        ∫ h' in D, Ê (e (h, h')) * detInv χ h' * φ h' ∂μ = ∫ g, f (e (1, g)) * detInv χ g * φ (h * g) ∂μ
def HgtInt_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, _root_.UpperTheory.TP.W.GoodK σ B → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K a (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → IsHgt K a → (∀ h h', IsEmb h h' (e (h, h'))) →
    ∀ μ : Measure (UA σ Y.J), μ.IsHaarMeasure → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => a (e (1, g)) ^ t) μ
end GlobalTheory.ThK.Dbl
end
end
end
