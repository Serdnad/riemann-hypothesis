module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle009
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle008
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.isBes_tensor_projection_and_ev_equivariant_smooth : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (om : ι → ℂ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ρ s *ᵥ om = om) → ∀ I, (∀ lI, IsBes (RI I) z π lI → IsBes R z π (fun v => lI (∑ c, pr I c (tm R om v c)))) ∧ (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ y ∈ (RI I).sm, ev Γ R om (fun c => io I c ((RI I).σ s y)) = R.σ s (ev Γ R om (fun c => io I c y))) ∧ SmMap (RI I) R (fun y => ev Γ R om (fun c => io I c y)) := by
  first | exact @GlobalTheory.KapBes.main | exact GlobalTheory.KapBes.main | (intros; apply GlobalTheory.KapBes.main <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.smoothVectors_discreteSeries_glModule : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  first | exact @GlobalTheory.smooth_gl_module | exact GlobalTheory.smooth_gl_module | (intros; apply GlobalTheory.smooth_gl_module <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.tensor_decomposition_injective_parameters : HypsG → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∃ io' pr' ep, TensH ρ Γ R RI io' pr' ep := by
  first | exact @GlobalTheory.TensOrth.tensH_of_raw | exact GlobalTheory.TensOrth.tensH_of_raw | (intros; apply GlobalTheory.TensOrth.tensH_of_raw <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.cayley_endomorphisms_unitary : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  first | exact @GlobalTheory.CapUnitary.isUnitary_of_isE | exact GlobalTheory.CapUnitary.isUnitary_of_isE | (intros; apply GlobalTheory.CapUnitary.isUnitary_of_isE <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.derivedAction_expand_matrixUnits : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  first | exact @GlobalTheory.dC_expand_units | exact GlobalTheory.dC_expand_units | (intros; apply GlobalTheory.dC_expand_units <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDG ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  first | exact @GlobalTheory.quotMeas_ae_mem_and_measurable | exact GlobalTheory.quotMeas_ae_mem_and_measurable | (intros; apply GlobalTheory.quotMeas_ae_mem_and_measurable <;> assumption)
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
namespace CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → E) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → E) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [Formalism.REAL.RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem sum_mem {ι : Type} (A : ℝ) (f : ι → B.Mat k r → E) (t : Finset ι)
    (hf : ∀ i ∈ t, B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC A m (f i)) :
    B.CkOn ⊤ (B.GV k r) (∑ i ∈ t, f i) ∧ ∀ m : ℕ, B.InCC A m (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      fun m => ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩⟩
    intro u v _ _ _ g _
    simp [dLR_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨h1, h2⟩ := hf i (Finset.mem_insert_self _ _)
    obtain ⟨h3, h4⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨Formalism.FourierDecayAlt.P.B4.ckOn_add h1 h3, fun m => ?_⟩
    obtain ⟨c, hc⟩ := h2 m
    obtain ⟨c', hc'⟩ := h4 m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r E A m _ _ c c' 1 hc hc').1⟩

end CoefDecay

theorem isCoef_ckOn_inCC : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsCoef R l l' F s → B.CkOn ⊤ (B.GV k r) F ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m F := by
  intro hH k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ l l' F s hR hg hok hF
  obtain ⟨n, x, y, X, hxy, hFe, -⟩ := hF
  have hK : PI.KFinSmooth := hH.1.2.2.1
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  let f : Fin n → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      B.CkOn ⊤ (B.GV k r) (f i) ∧ ∀ m : ℕ, B.InCC (aOf r h - 1) m (f i) := by
    intro i _
    obtain ⟨h1, h2⟩ := GlobalTheory.T.matrix_coefficient_smooth_derivatives hK k r ε mu R (Wq →L[ℂ] Wp) (X i) (f i) hR (x i) (hsm _ (hxy i).1)
      (y i) (hsm _ (hxy i).2) (fun g _ => rfl)
    refine ⟨h1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrix_coefficient_decay hH k r ε mu h R hR hg hok (x i) (hxy i).1 (y i) (hxy i).2 m
    refine ⟨c * ‖X i‖, Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top h1, fun u v hu hv hlen g hgG => ?_⟩
    rw [h2 u v (fun Y hY => (hu Y hY).1) (fun Y hY => (hv Y hY).1) g hgG, norm_smul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hc u v hu hv hlen g hgG) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := CoefDecay.sum_mem (aOf r h - 1) f Finset.univ hf
  have hc := GlobalTheory.ckOn_inCC_congr_on_group k r (Wq →L[ℂ] Wp) (aOf r h - 1) (∑ i, f i) F
    (fun g hgG => by rw [hFe g hgG, Finset.sum_apply])
  exact ⟨hc.1 h1, fun m => hc.2 m (h2 m)⟩

end GlobalTheory
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.RawTens

def lm {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) : R.smSub →ₗ[ℂ] R'.smSub where
  toFun v := ⟨T v, h.mem v v.2⟩
  map_add' v w := Subtype.ext (h.add v v.2 w w.2)
  map_smul' a v := Subtype.ext (h.smul a v v.2)

@[simp] theorem lm_coe {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) (v : R.smSub) :
    ((lm h v : R'.smSub) : R'.H) = T v := rfl

section alg

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem change_inv (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (x : Fin n → M) (c : Fin n) :
    ∑ d, B d c • ∑ e, A e d • x e = x c := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have : ∀ e, ∑ d, B d c * A e d = (1 : Matrix (Fin n) (Fin n) ℂ) e c := by
    intro e
    rw [← h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  simp_rw [this]
  simp [Matrix.one_apply]

theorem dualTens_sum {ι : Type} (S : Finset ι) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n)
    (x : ι → Fin n → M) : dualTens E a b (∑ i ∈ S, x i) = ∑ i ∈ S, dualTens E a b (x i) := by
  funext i
  by_cases h : i = b <;> simp [dualTens, Finset.sum_apply, h, map_sum, Finset.sum_sub_distrib]

theorem alg {N : Fin n → Type} [∀ s, AddCommGroup (N s)] [∀ s, Module ℂ (N s)]
    (I : ∀ s, Fin n → N s →ₗ[ℂ] M) (P : ∀ s, Fin n → M →ₗ[ℂ] N s)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hAB : A * B = 1) (hBA : B * A = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s))
    (hI : ∀ s a b y c, I s c (F s a b y) =
      E a b (I s c y) - ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y)
    (h1 : ∀ (x : Fin n → M) c, ∑ s, I s c (∑ d, P s d (x d)) = x c)
    (h2 : ∀ s y, ∑ c, P s c (I s c y) = y)
    (h3 : ∀ s t, s ≠ t → ∀ y, ∑ c, P s c (I t c y) = 0) :
    ∃ (io' : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s),
      (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧
      (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧
      (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧
      (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧
      (∀ s y d, io' s y d = ∑ c, B c d • I s c y) ∧
      ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
  let io' : ∀ s, N s →ₗ[ℂ] (Fin n → M) := fun s => LinearMap.pi fun d => ∑ c, B c d • I s c
  let pr' : ∀ s, (Fin n → M) →ₗ[ℂ] N s := fun s =>
    ∑ c, (P s c).comp (∑ d, A d c • LinearMap.proj d)
  have e1 : ∀ s y d, io' s y d = ∑ c, B c d • I s c y := by
    intro s y d
    simp [io', LinearMap.sum_apply]
  have e2 : ∀ s x, pr' s x = ∑ c, P s c (∑ d, A d c • x d) := by
    intro s x
    simp only [pr', LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.proj_apply]
  have c1 : ∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y) := by
    intro s a b y
    funext d
    have hY : ∀ j c, (B * Matrix.single a b (1 : ℂ) * A) j c = A b c * B j a := by
      intro j c
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single a]
      · simp [mul_comm]
      · intro e _ he
        simp [Matrix.single_mul_apply_of_ne, he]
      · simp
    have hz : ∀ c, ∑ j, (B * Matrix.single a b (1 : ℂ) * A) j c • I s j y = A b c • io' s y a := by
      intro c
      rw [e1, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hY, mul_smul]
    have hd : ∑ c, B c d * A b c = if d = b then 1 else 0 := by
      have : ∑ c, B c d * A b c = (A * B) b d := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun d _ => mul_comm _ _
      rw [this, hAB, Matrix.one_apply]
      simp [eq_comm]
    simp only [dualTens]

    rw [e1, e1 s y d, map_sum]
    simp_rw [hI, hz, smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, hd, map_smul]
    by_cases h : d = b <;> simp [h]
  have c3 : ∀ x, ∑ s, io' s (pr' s x) = x := by
    intro x
    funext d
    rw [Finset.sum_apply]
    simp_rw [e1, e2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, h1]
    exact change_inv A B hAB x d
  have c4 : ∀ s y, pr' s (io' s y) = y := by
    intro s y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h2 s y
  have c5 : ∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0 := by
    intro s t hst y
    rw [e2]
    simp_rw [e1, change_inv B A hBA]
    exact h3 s t hst y
  refine ⟨io', pr', c1, ?_, c3, c4, c5, e1, e2⟩
  intro s a b x
  conv_lhs => rw [← c3 x]

  rw [dualTens_sum, map_sum, Finset.sum_eq_single s]
  · rw [← c1, c4]
  · intro t _ ht
    rw [← c1, c5 s t (Ne.symm ht)]
  · simp

end alg

theorem rawTens : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (RI : Fin (2 * r + k + 1) → Rep k r) (muI : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)) (F : ∀ s, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (RI s).smSub), (∀ s, (RI s).IsDG ε (muI s)) → TensRaw dualM R RI io pr → IsUnit Q → R.IsE Q E → (∀ s, (RI s).IsE Q (F s)) → ∃ (io' : ∀ s, (RI s).smSub →ₗ[ℂ] (Fin (2 * r + k + 1) → R.smSub)) (pr' : ∀ s, (Fin (2 * r + k + 1) → R.smSub) →ₗ[ℂ] (RI s).smSub), (∀ s a b y, io' s (F s a b y) = dualTens E a b (io' s y)) ∧ (∀ s a b x, pr' s (dualTens E a b x) = F s a b (pr' s x)) ∧ (∀ x, ∑ s, io' s (pr' s x) = x) ∧ (∀ s y, pr' s (io' s y) = y) ∧ (∀ s t, s ≠ t → ∀ y, pr' s (io' t y) = 0) ∧ (∀ s y d, ((io' s y d : R.smSub) : R.H) = ∑ c, Q⁻¹ c d • io s c (y : (RI s).H)) ∧ ∀ s x, ((pr' s x : (RI s).smSub) : (RI s).H) = ∑ c, pr s c (∑ d, Q d c • ((x d : R.smSub) : R.H)) := by
  intro hK k r ε mu R hR RI muI io pr Q E F hRI hT hQ hE hF
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ
  obtain ⟨io', pr', c1, c2, c3, c4, c5, e1, e2⟩ :=
    alg (N := fun s => (RI s).smSub) (fun s c => lm (hT.io_sm s c)) (fun s c => lm (hT.pr_sm s c)) Q Q⁻¹
      (Matrix.mul_nonsing_inv Q hdet) (Matrix.nonsing_inv_mul Q hdet) E F
      (by
        intro s a b y c
        apply Subtype.ext
        rw [lm_coe, hF s a b y, GlobalTheory.T.dual_tensor_capelli_intertwine hK k r ε mu R hR RI muI io pr hRI hT s _ y y.2 c,
          Submodule.coe_sub, hE a b, Submodule.coe_sum]
        rfl)
      (by
        intro x c
        apply Subtype.ext
        have := hT.sum_io_pr (fun d => (x d : R.H)) (fun d => (x d).2) c
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s y
        apply Subtype.ext
        have := hT.pr_io s y y.2
        simpa only [Submodule.coe_sum, lm_coe] using this)
      (by
        intro s t hst y
        apply Subtype.ext
        have := hT.pr_io_ne s t hst y y.2
        simpa only [Submodule.coe_sum, lm_coe, Submodule.coe_zero] using this)
  refine ⟨io', pr', c1, c2, c3, c4, c5, ?_, ?_⟩
  · intro s y d
    rw [e1]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]
  · intro s x
    rw [e2]
    simp only [Submodule.coe_sum, lm_coe, Submodule.coe_smul]

end GlobalTheory.RawTens
end
end Gp91
end
