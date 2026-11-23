module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle125
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle129
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableHsNormSqAmplitudeBesselUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ContRepUniq

theorem lintegral_enorm_sq_eq {X : Type} [MeasurableSpace X] (μ : Measure X) (F : Lp ℂ 2 μ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable F)]
  have h2 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [h2, ← ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem contRep_unique_linear : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  intro B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F f f' hf hf'
    exact ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.1 f' hf').symm
  · intro F F' f f' c hf hf'
    refine ⟨hf.1.add (continuous_const.mul hf'.1), ?_, ?_⟩
    · intro γ hγ x
      show f (γ * x) + c * f' (γ * x) = f x + c * f' x
      rw [hf.2.1 γ hγ x, hf'.2.1 γ hγ x]
    · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', hf.2.2, hf'.2.2]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
  · intro F f g hf
    exact (GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.2.1 g
  · intro F f hf
    refine ⟨(GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).1.symm, ?_⟩
    refine Eq.trans ?_ (lintegral_enorm_sq_eq ((B.I.muA B.μf).restrict B.fund) F)
    refine lintegral_congr_ae ?_
    filter_upwards [hf.2.2] with x hx
    rw [hx]

end GlobalTheory.ContRepUniq
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem kerDiag_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y : Fin D → H) (hy : Orthonormal ℂ y) (v : H) (hv : v ∈ Submodule.span ℂ (Set.range y)) :
    v = ∑ i, ⟪y i, v⟫_ℂ • y i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy.inner_right_fintype]

theorem kerDiag_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y y' : Fin D → H) (hy : Orthonormal ℂ y) (hy' : Orthonormal ℂ y') (a b : Fin D → ℂ)
    (hb : ∀ j, b j = ∑ i, ⟪y i, y' j⟫_ℂ * a i) :
    ∑ j, ‖b j‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu
  have h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖ := by
    intro j
    rw [norm_inner_symm, hb, hu, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_conj, mul_comm]
  have h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    have h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hu, hy.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [inner_self_eq_norm_sq_to_K] at h3
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← h3, Complex.ofReal_pow]
    rfl
  simp only [h1]
  rw [← h2]
  exact hy'.sum_inner_products_le u

theorem kerDiag_add_rep (B : RowsAut) (F F' : B.I.L2 B.μf B.fund) (f f' : B.I.GA → ℂ) (c : ℂ)
    (h : IsContRep B F f) (h' : IsContRep B F' f') :
    IsContRep B (F + c • F') (fun x => f x + c * f' x) := by
  refine ⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩
  · simp only [h.2.1 γ hγ x, h'.2.1 γ hγ x]
  · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem kerDiag_sum_rep (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (f : ι → B.I.GA → ℂ) (c : ι → ℂ) (F : B.I.L2 B.μf B.fund) (g : B.I.GA → ℂ)
    (hg : IsContRep B F g) (h : ∀ i, IsContRep B (y i) (f i)) :
    IsContRep B (F + ∑ i ∈ s, c i • y i) (fun x => g x + ∑ i ∈ s, c i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have := kerDiag_add_rep B _ _ _ _ (c a) ih (h a)
    simp only [Finset.sum_insert ha]
    convert this using 1
    · abel
    · funext x; ring

theorem kerDiag_vals (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund)
    (f f' : Fin D → B.I.GA → ℂ) (hy : Orthonormal ℂ y)
    (hs : Submodule.span ℂ (Set.range y') ≤ Submodule.span ℂ (Set.range y))
    (h : ∀ i, IsContRep B (y i) (f i)) (h' : ∀ i, IsContRep B (y' i) (f' i)) (j : Fin D)
    (x : B.I.GA) : f' j x = ∑ i, ⟪y i, y' j⟫_ℂ * f i x := by
  have e := kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))
  have h1 := kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h
  rw [← e] at h1
  have h2 := kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)
  rw [one_smul] at h2
  have h3 := congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x
  simp only [one_mul, add_right_inj] at h3
  exact h3.symm

theorem kerDiag_basis_indep : ∀ (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund) (f f' : Fin D → B.I.GA → ℂ), Orthonormal ℂ y → Orthonormal ℂ y' → Submodule.span ℂ (Set.range y) = Submodule.span ℂ (Set.range y') → (∀ i, IsContRep B (y i) (f i) ∧ IsContRep B (y' i) (f' i)) → ∀ x, ∑ i, ‖f i x‖ ^ 2 = ∑ i, ‖f' i x‖ ^ 2 := by
  intro B D y y' f f' hy hy' hs h x
  apply le_antisymm
  · exact kerDiag_le y' y hy' hy _ _ fun j =>
      kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x
  · exact kerDiag_le y y' hy hy' _ _ fun j =>
      kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x

end GlobalTheory.Dec
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W → ∃ (a : ℝ → UJ ε) (Hm : Matrix (Fin n) (Fin n) ℂ), inP ε Hm ∧ (∀ s : ℝ, umat (a s) = NormedSpace.exp ((s : ℂ) • Hm)) ∧ (∀ s, dOp (umat (a s)) ≤ |s|) ∧ (∀ s, ∀ m ∈ NW ε W, a s * m * (a s)⁻¹ ∈ NW ε W ∧ |s| ≤ dOp (umat (m * a s))) ∧ (∀ m ∈ NW ε W, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) ∧ ∀ g : UJ ε, ∃ k : UJ ε, umat k ∈ Kset ε ∧ ∀ s, a s * g * (k⁻¹ * a s * k)⁻¹ * g⁻¹ ∈ NW ε W := by
  first | exact @GlobalTheory.IsoTorus.split_torus | exact GlobalTheory.IsoTorus.split_torus | (intros; apply GlobalTheory.IsoTorus.split_torus <;> assumption)
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PointLattice

theorem conj_mulVec_eq_smul (I : AutInst) (x : I.GA) (c : ℕ) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (hM : ∀ y ∈ lamX I x, ∃ z ∈ lamX I x, M *ᵥ y = (c : I.E) • z)
    (w : Fin I.n → I.E ⊗[I.F] Af I.F) (hw : w ∈ I.Lf) :
    ∃ z ∈ I.Lf, (I.fmat x.2⁻¹ * M.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * I.fmat x.2) *ᵥ w =
      (c : I.E ⊗[I.F] Af I.F) • z := by
  have e1 : Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L = I.Lf := by
    unfold Formalism.UG.latS AutInst.Lf lamAf
    rw [Set.image_eq_range]
    rfl
  have hfin := Module.Finite.iff_fg.2 I.L_fg
  have hu := Formalism.UG.P.csSpan_back Formalism.UG.P.csGlob_intAdApprox I.L hfin I.L_span
    (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (I.fmat x.2 *ᵥ w)
    (by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]; exact e1.symm ▸ hw)
  rw [← lamX_eq_globLat] at hu
  rw [← mulVec_mulVec]
  generalize I.fmat x.2 *ᵥ w = u at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨z, hz, e⟩ := hM y hy
    refine ⟨_, (GlobalTheory.Count.Test.mem_lamX I x z).1 hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_smul]
    congr 1
    funext i
    have h := (RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F) : I.E →+* _) M y i).symm
    rw [e] at h
    refine h.trans ?_
    simp
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨z, hz, e⟩ := hu
    obtain ⟨z', hz', e'⟩ := hv
    exact ⟨z + z', add_mem hz hz', by rw [mulVec_add, e, e', smul_add]⟩
  | smul s u _ hu =>
    obtain ⟨z, hz, e⟩ := hu
    refine ⟨s • z, Submodule.smul_mem _ s hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, mulVec_smul, e, smul_comm]

theorem conj_mem_Kg_of_congr : ∀ (I : AutInst) (x a : I.GA) (g : ℕ) (γ : GL (Fin I.n) I.E), I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → (∀ y ∈ lamX I x, ∃ z ∈ lamX I x, ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) *ᵥ y = (g : I.E) • z) → (∀ y ∈ lamX I x, ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I x) → (x⁻¹ * a * x).2 ∈ I.Kg g := by
  intro I x a g γ ha h1 h2
  have hk : I.fmat (x⁻¹ * a * x).2 = I.fmat x.2⁻¹ * I.fmat a.2 * I.fmat x.2 := rfl
  have hx1 : I.fmat x.2⁻¹ * I.fmat x.2 = 1 := Units.inv_mul _
  have hx2 : I.fmat x.2 * I.fmat x.2⁻¹ = 1 := Units.mul_inv _
  have hc : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (x⁻¹ * a * x).2 - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
    intro y hy
    obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x g _ h1 y hy
    refine ⟨z, hz, ?_⟩
    rw [← e, hk, ha, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      mul_sub, sub_mul, mul_one, hx1]
  refine ⟨fun y => ?_, hc⟩
  symm
  show I.fmat (x⁻¹ * a * x).2 *ᵥ y ∈ I.Lf ↔ y ∈ I.Lf
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨z, hz, e⟩ := conj_mulVec_eq_smul I x 1 _
      (fun y hy => ⟨_, h2 y hy, by rw [Nat.cast_one, one_smul]⟩) _ hy
    rw [Nat.cast_one, one_smul, mulVec_mulVec, hk, ha] at e
    have hγ : ((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
      rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : ∀ A B C D : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F), A * B = 1 → B * A = 1 →
        C * D = 1 → A * C * B * (A * D * B) = 1 := by
      intro A B C D p q r
      calc A * C * B * (A * D * B) = A * (C * (B * A) * D) * B := by simp only [mul_assoc]
        _ = 1 := by rw [q, mul_one, r, mul_one, p]
    rw [h3 _ _ _ _ hx1 hx2 hγ, one_mulVec] at e
    exact e ▸ hz
  · obtain ⟨z, hz, e⟩ := hc y hy
    rw [sub_mulVec, one_mulVec, sub_eq_iff_eq_add, Nat.cast_smul_eq_nsmul] at e
    rw [e]
    exact add_mem (nsmul_mem hz g) hy

end GlobalTheory.PointLattice
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.BallVol

lemma entry_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2)
    (i j : Fin n) : ‖g i j‖ ≤ R :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 ((f1auxiliary_entry_le g i j).trans hg)

lemma inv_mul_uMat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  have : uMat g⁻¹ * uMat g = uMat (g⁻¹ * g) := rfl
  rw [this, inv_mul_cancel]; rfl

lemma norm_inv_entry {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (i k : Fin n) :
    ‖uMat g⁻¹ i k‖ = ‖uMat g k i‖ := by
  have h1 := (uJInv n ε (uMat g) g.2).1
  have h2 : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (Jm ε * (uMat g)ᴴ * Jm ε)) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, inv_mul_uMat, Matrix.one_mul]
  rw [h2]
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

lemma close_entry {n : ℕ} {ε : Fin n → Bool} (g t : UJ ε) {R : ℝ} (hR : 0 < R)
    (ht : hsG t ≤ R ^ 2) (j : Fin n) (hj : ∀ k, ‖uMat g k j - uMat t k j‖ ≤ 1 / R) (i : Fin n) :
    ‖uMat (t⁻¹ * g) i j‖ ≤ 1 + n := by
  have e : uMat (t⁻¹ * g) = 1 + uMat t⁻¹ * (uMat g - uMat t) := by
    rw [Matrix.mul_sub, inv_mul_uMat]
    have : uMat (t⁻¹ * g) = uMat t⁻¹ * uMat g := rfl
    rw [this]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  have h3 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine (norm_add_le _ _).trans (add_le_add h3 ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖uMat t⁻¹ i k * (uMat g - uMat t) k j‖ ≤ ∑ _k : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_inv_entry, Matrix.sub_apply]
        calc _ ≤ R * (1 / R) :=
              mul_le_mul (entry_le hR.le ht k i) (hj k) (norm_nonneg _) hR.le
          _ = 1 := by field_simp
    _ = n := by simp

lemma vol_sign (n : ℕ) (ε : Fin n → Bool) (s : Bool) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤
      ENNReal.ofReal (C * R ^ (4 * n * (univ.filter fun a => ε a = s).card)) := by
  classical
  set q := (univ.filter fun a => ε a = s).card with hq
  let E := Fin n → {j // ε j = s} → ℂ
  have hfr : Module.finrank ℝ E = 2 * n * q := by
    simp only [E, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_subtype, ← hq]
    ring
  let Y : UJ ε → E := fun g i j => uMat g i j.1
  let W : Set (UJ ε) := {g | hsG g ≤ n + 4 * (n * (n * (1 + n) ^ 2))}
  have hW : muG ε W < ⊤ := ballFinite n ε _
  refine ⟨3 ^ (2 * n * q) * (muG ε W).toReal, by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hsub : Y '' S ⊆ Metric.closedBall 0 R := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR0.le]
    intro j
    exact entry_le hR0.le hg i j.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_net_card_le_of_subset_closedBall E (Y '' S) R (1 / R) (by positivity) hR0.le hsub
  have hch : ∀ x : E, ∃ t : UJ ε, x ∈ T → t ∈ S ∧ Y t = x := by
    intro x
    by_cases hx : x ∈ T
    · obtain ⟨t, ht, rfl⟩ := hT1 hx
      exact ⟨t, fun _ => ⟨ht, rfl⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose τ hτ using hch
  have hcov : S ⊆ ⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W := by
    intro g hg
    obtain ⟨x, hx, hd⟩ := hT3 (Y g) ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := hτ x hx
    simp only [Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    show hs (uMat ((τ x)⁻¹ * g)) ≤ _
    refine (GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns n ε s _ ((τ x)⁻¹ * g).2).trans ?_
    gcongr
    calc ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖uMat ((τ x)⁻¹ * g) i j‖ ^ 2
        ≤ ∑ _i : Fin n, ∑ _j ∈ univ.filter (fun j => ε j = s), ((1 : ℝ) + n) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine close_entry g (τ x) hR0 h1 j (fun k => ?_) i
          have hj' : ε j = s := (Finset.mem_filter.1 hj).2
          rw [← h2, dist_eq_norm] at hd
          exact ((norm_le_pi_norm ((Y g - Y (τ x)) k) ⟨j, hj'⟩).trans
            (norm_le_pi_norm (Y g - Y (τ x)) k)).trans hd
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((1 : ℝ) + n) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) := by
    refine hT2.trans ?_
    rw [hfr, show 4 * n * q = 2 * (2 * n * q) by ring, pow_mul R, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : 2 * R / (1 / R) = 2 * R ^ 2 := by field_simp
    rw [this]; nlinarith
  calc muG ε S ≤ muG ε (⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_mono hcov
    _ ≤ ∑ x ∈ T, muG ε ((fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ T, muG ε W := Finset.sum_congr rfl fun x _ => measure_preimage_mul _ _ _
    _ = ENNReal.ofReal ((T.card : ℝ) * (muG ε W).toReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hW.ne, ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (T.card : ℝ) * (muG ε W).toReal
            ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) * (muG ε W).toReal := by gcongr
          _ = _ := by ring

lemma hs_le_of_dOp {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (h : dOp g ≤ r) :
    hs g ≤ ((n + 1) * Real.exp r) ^ 2 := by
  have h1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ ≤ Real.exp r :=
    Real.le_exp_of_log_le h
  have h2 : ∀ i j, ‖g i j‖ ≤ Real.exp r := by
    intro i j
    have h3 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm
      (EuclideanSpace.single j (1 : ℂ))
    have h4 := PiLp.norm_apply_le ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ))) i
    have h5 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ)) i = g i j := by
      simp [Matrix.toLpLin_apply]
    rw [h5] at h4
    have h6 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
    rw [h6, mul_one] at h3
    exact h4.trans (h3.trans h1)
  have hp := Real.exp_pos r
  calc hs g ≤ ∑ _i : Fin n, ∑ _j : Fin n, Real.exp r ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h2 i j) 2
    _ = (n * Real.exp r) ^ 2 := by simp; ring
    _ ≤ _ := by gcongr; linarith

theorem ballVol : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  intro n ε
  obtain ⟨s, hs'⟩ : ∃ s : Bool, rkR ε = (univ.filter fun a => ε a = s).card := by
    unfold rkR
    rcases min_choice (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨C, hC, h⟩ := vol_sign n ε s
  rw [← hs'] at h
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn' : (1 : ℝ) ≤ (n + 1) ^ (4 * n * rkR ε) := one_le_pow₀ hn
  refine ⟨C * (n + 1) ^ (4 * n * rkR ε), fun R hR => (h R hR).trans ?_, fun r hr => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ R ^ (4 * n * rkR ε) := by positivity
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hn') this
  · have he : 1 ≤ Real.exp r := Real.one_le_exp hr
    have h1 := h ((n + 1) * Real.exp r) (one_le_mul_of_one_le_of_one_le hn he)
    refine (measure_mono fun g hg => ?_).trans (h1.trans (le_of_eq ?_))
    · exact hs_le_of_dOp hg
    · rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc]
      push_cast
      rfl

end GlobalTheory.BallVol
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.flagLayerProductMeasure_mul_prod_local : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ) (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) → layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  first | exact @GlobalTheory.FlagMeas.layerProd_mul_prod | exact GlobalTheory.FlagMeas.layerProd_mul_prod | (intros; apply GlobalTheory.FlagMeas.layerProd_mul_prod <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

theorem _root_.GlobalTheory.T.autPointMajorantFrames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  first | exact @GlobalTheory.Count.FrameMajorant.frames_give_majorants | exact GlobalTheory.Count.FrameMajorant.frames_give_majorants | (intros; apply GlobalTheory.Count.FrameMajorant.frames_give_majorants <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  first | exact @GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | exact GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | (intros; apply GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le <;> assumption)
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (μG : Measure (Mt k r)) (c : ℝ) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → Measurable (Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun γ => hsNormSq (ampJ μG c Φ Φ' (Matrix.of γ))) := by
  first | exact @GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | exact GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ | (intros; apply GlobalTheory.Amp.AmpMeas.measurable_hsNormSq_ampJ <;> assumption)
end
