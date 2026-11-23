module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle213
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle211
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem exists_intertwiner_decomp_of_kernel_intertwines {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h5 : vecMulVec x u + A * A' = 1) (z : Fin n → R) :
    z = (u ⬝ᵥ z) • x + A *ᵥ (A' *ᵥ z) := by
  have h : (vecMulVec x u + A * A') *ᵥ z = z := by rw [h5, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at h
  conv_lhs => rw [← h]
  congr 1
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem coords_smul_add_mulVec {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1) (a : R) (w : Fin m → R) :
    u ⬝ᵥ (a • x + A *ᵥ w) = a ∧ A' *ᵥ (a • x + A *ᵥ w) = w := by
  constructor
  · rw [dotProduct_add, dotProduct_smul, h4, Matrix.dotProduct_mulVec, h3, zero_dotProduct, smul_eq_mul,
      mul_one, add_zero]
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, smul_zero,
      zero_add]

theorem conj_stab_and_cong_of_split {R : Type} [CommRing R] (S : Subring R) {n m : ℕ}
    (L : Submodule S (Fin n → R)) (L' : Submodule S (Fin m → R))
    (X Xi G : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) R)
    (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (hX : X * Xi = 1) (hXi : Xi * X = 1)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1)
    (h5 : vecMulVec x u + A * A' = 1)
    (hL : ∀ z, Xi *ᵥ z ∈ L ↔ ∃ a ∈ S, ∃ w ∈ L', z = a • x + A *ᵥ w)
    (hGx : G *ᵥ x = x) (hGA : G * A = A * g) :
    ((∀ w, w ∈ L' ↔ g *ᵥ w ∈ L') ↔ ∀ y, y ∈ L ↔ (Xi * G * X) *ᵥ y ∈ L) ∧
      ∀ c : R, (∀ w ∈ L', ∃ w' ∈ L', (g - 1) *ᵥ w = c • w') ↔
        ∀ y ∈ L, ∃ z ∈ L, (Xi * G * X - 1) *ᵥ y = c • z := by
  have hu0 : ∀ w, u ⬝ᵥ (A *ᵥ w) = 0 := fun w => by
    rw [Matrix.dotProduct_mulVec, h3, zero_dotProduct]
  have hA0 : ∀ w, A' *ᵥ (A *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hM : ∀ z, Xi *ᵥ z ∈ L ↔ u ⬝ᵥ z ∈ S ∧ A' *ᵥ z ∈ L' := by
    intro z
    rw [hL]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨e1, e2⟩ := coords_smul_add_mulVec x u A A' h1 h2 h3 h4 a w
      rw [e1, e2]
      exact ⟨ha, hw⟩
    · rintro ⟨ha, hw⟩
      exact ⟨_, ha, _, hw, exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z⟩
  have hG : ∀ z, G *ᵥ z = (u ⬝ᵥ z) • x + A *ᵥ (g *ᵥ (A' *ᵥ z)) := by
    intro z
    conv_lhs => rw [exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGx, Matrix.mulVec_mulVec, hGA, ← Matrix.mulVec_mulVec]
  have hXiX : ∀ y, Xi *ᵥ (X *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec]
  have hXXi : ∀ y, X *ᵥ (Xi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]
  have hconj : ∀ y, (Xi * G * X) *ᵥ y = Xi *ᵥ (G *ᵥ (X *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hGm : ∀ p, (G - 1) *ᵥ p = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
    intro p
    have hp := exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 p
    calc (G - 1) *ᵥ p = G *ᵥ p - p := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = ((u ⬝ᵥ p) • x + A *ᵥ (g *ᵥ (A' *ᵥ p))) - ((u ⬝ᵥ p) • x + A *ᵥ (A' *ᵥ p)) := by
          rw [← hp, hG]
      _ = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
          abel
  have hsub : ∀ y, (Xi * G * X - 1) *ᵥ y = Xi *ᵥ (A *ᵥ ((g - 1) *ᵥ (A' *ᵥ (X *ᵥ y)))) := by
    intro y
    rw [← hGm]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, hconj, Matrix.one_mulVec, hXiX]
  refine ⟨⟨fun hg y => ?_, fun h w => ?_⟩, fun c => ⟨fun hc y hy => ?_, fun h w hw => ?_⟩⟩
  · rw [hconj y]
    conv_lhs => rw [← hXiX y]
    rw [hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2]
    exact Iff.and Iff.rfl (hg _)
  · have hw := h (Xi *ᵥ (A *ᵥ w))
    rw [hconj, hXXi, hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1,
      (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2, hu0, hA0] at hw
    simpa [S.zero_mem] using hw
  · rw [← hXiX y, hM] at hy
    obtain ⟨w', hw', hgw⟩ := hc _ hy.2
    refine ⟨Xi *ᵥ (A *ᵥ w'), ?_, ?_⟩
    · rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw'⟩
    · rw [hsub, hgw, Matrix.mulVec_smul, Matrix.mulVec_smul]
  · have hy : Xi *ᵥ (A *ᵥ w) ∈ L := by
      rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw⟩
    obtain ⟨z, hz, hcz⟩ := h _ hy
    rw [hsub, hXXi, hA0] at hcz
    have e := congrArg (fun v => A' *ᵥ (X *ᵥ v)) hcz
    simp only [hXXi, hA0, Matrix.mulVec_smul] at e
    refine ⟨A' *ᵥ (X *ᵥ z), ?_, e⟩
    have hz' : Xi *ᵥ (X *ᵥ z) ∈ L := by rw [hXiX]; exact hz
    exact ((hM _).1 hz').2

theorem mem_level_iff_of_isFinEmb (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (jf : D.inst.Gf →* I.Gf) (hj : IsFinEmb D x A jf) :
    (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧
      ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  obtain ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩ := hp
  have hJ : I.Jᴴ = I.J := by
    have h := I.J_herm
    unfold Formalism.UG.IsHerm at h
    conv_rhs => rw [← h]
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]
  have hβ' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]
    cases s <;> simp [sgn]
  obtain ⟨u, A', e1, e2, e3, e4, e5, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ' hxJA hAJA
  have h1 : afMat I A' * afMat I A = 1 := by
    simp only [afMat]
    rw [← Matrix.map_mul, e1, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have h2 : afMat I A' *ᵥ afVec I x = 0 := by
    funext i
    have := RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) A' x i
    rw [e2, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : afVec I u ᵥ* afMat I A = 0 := by
    funext i
    have := RingHom.map_vecMul (Formalism.UG.inclE (F := I.F) (Af I.F)) A u i
    rw [e3, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h4 : afVec I u ⬝ᵥ afVec I x = 1 := by
    have := RingHom.map_dotProduct (Formalism.UG.inclE (F := I.F) (Af I.F)) u x
    rw [e4, map_one] at this
    exact this.symm
  have h5 : vecMulVec (afVec I x) (afVec I u) + afMat I A * afMat I A' = 1 := by
    have hv : vecMulVec (afVec I x) (afVec I u) = (vecMulVec x u).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp [afVec, vecMulVec]
    rw [hv]
    simp only [afMat]
    rw [← Matrix.map_mul, ← Matrix.map_add _ (map_add (Formalism.UG.inclE (F := I.F) (Af I.F))), e5, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have hX : I.fmat xf * I.fmat xf⁻¹ = 1 := by simp [AutInst.fmat]
  have hXi : I.fmat xf⁻¹ * I.fmat xf = 1 := by simp [AutInst.fmat]
  have hprod : ∀ g, I.fmat (xf⁻¹ * jf g * xf) = I.fmat xf⁻¹ * I.fmat (jf g) * I.fmat xf := by
    intro g
    simp [AutInst.fmat]
  have key := fun g => conj_stab_and_cong_of_split (IntAf I.F I.E) I.Lf D.inst.Lf (I.fmat xf) (I.fmat xf⁻¹)
    (I.fmat (jf g)) (D.inst.fmat g) (afVec I x) (afVec I u) (afMat I A) (afMat I A') hX hXi h1 h2 h3 h4 h5
    (adelicLattice_split I D s x A xf ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩) (hj g).1 (hj g).2
  have hK : ∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset := by
    intro g
    show (∀ w, w ∈ D.inst.Lf ↔ D.inst.fmat g *ᵥ w ∈ D.inst.Lf) ↔
      ∀ y, y ∈ I.Lf ↔ I.fmat (xf⁻¹ * jf g * xf) *ᵥ y ∈ I.Lf
    rw [hprod]
    exact (key g).1
  refine ⟨hK, fun N g => ?_⟩
  show (g ∈ D.inst.Kset ∧ ∀ y ∈ D.inst.Lf, ∃ z ∈ D.inst.Lf,
      (D.inst.fmat g - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z) ↔
    (xf⁻¹ * jf g * xf ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (xf⁻¹ * jf g * xf) - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z)
  rw [hprod]
  exact Iff.and (hK g) ((key g).2 _)

end GlobalTheory.StabUnfold
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.measure_commonStabilizerCoords_box_image : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  first | exact @GlobalTheory.DegVol.RefMeas.box_meas | exact GlobalTheory.DegVol.RefMeas.box_meas | (intros; apply GlobalTheory.DegVol.RefMeas.box_meas <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  first | exact @GlobalTheory.DegVol.RefCov.atP_measurePreserving | exact GlobalTheory.DegVol.RefCov.atP_measurePreserving | (intros; apply GlobalTheory.DegVol.RefCov.atP_measurePreserving <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.T.commonStabilizerFromCoordinates_product_law : ∀ (k r j : ℕ) (β : Fin r → ℕ), crd k r j β 0 = 1 ∧ ∀ p q w : (UTin β → ℂ) × PTop k r j, crd k r j β p * crd k r j β q = crd k r j β w → (∀ i : UTin β, (∀ l : UTin β, l.1.1.2.val - l.1.1.1.val < i.1.1.2.val - i.1.1.1.val → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2) := by
  first | exact @GlobalTheory.DegVol.RefCovMul.crd_mul | exact GlobalTheory.DegVol.RefCovMul.crd_mul | (intros; apply GlobalTheory.DegVol.RefCovMul.crd_mul <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem kfin_zero {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsKFinHpk (k := k) (r := r) σ 0 :=
  ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]⟩

theorem isCoef_zero {k r : ℕ} (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) :
    IsCoef (rep L) l l' (fun _ => 0) 0 :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun g _ => by simp, by simp⟩

end GlobalTheory.AmpTK
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwNear

open GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem nrm_J_conj (X : Matrix (Fin n) (Fin n) ℂ) : nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by
  unfold nrm Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

private theorem uMat_inv_eq_Jm_conjTranspose_Jm (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hg : (uMat g)ᴴ * (Formalism.REAL.Jm ε * uMat g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by simp [uMat]
  have h2 : Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, J_sq]
  calc uMat g⁻¹ = (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
        rw [h2, Matrix.one_mul]
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := Matrix.mul_assoc _ _ _
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h1, Matrix.mul_one]

theorem nrm_inv (g : Formalism.REAL.UJ ε) : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
  have e : uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
    rw [uMat_inv_eq_Jm_conjTranspose_Jm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, J_sq]
  rw [e, nrm_J_conj, nrm_conjTranspose]

theorem nrm_mul_sub_one (g h : Formalism.REAL.UJ ε) :
    nrm (uMat (g * h) - 1) ≤ nrm (uMat g - 1) * nrm (uMat h - 1) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
  have e : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
    rw [show uMat (g * h) = uMat g * uMat h from rfl]
    noncomm_ring
  rw [e]
  calc _ ≤ nrm ((uMat g - 1) * (uMat h - 1) + (uMat g - 1)) + nrm (uMat h - 1) := nrm_add_le _ _
    _ ≤ nrm ((uMat g - 1) * (uMat h - 1)) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
        gcongr
        exact nrm_add_le _ _
    _ ≤ _ := by
        gcongr
        exact nrm_mul_le _ _

theorem nrm_levi_le {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    {u m : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε W) (hm : m ∈ flagM ε W) :
    nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := by

  obtain ⟨hN, hM⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, -, -, hmul⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hX := hN u hu
  obtain ⟨hm1, hm2⟩ := hM m hm
  have hY : uMat m * (uMat m)ᴴ - uMat m ∈ keeps ε W := sub_mem (hmul _ hm1 _ hm2) hm1
  have e : uMat (u * m) - 1 = (uMat u - 1) * uMat m + (uMat m - 1) := by
    rw [show uMat (u * m) = uMat u * uMat m from rfl]
    noncomm_ring
  have key : ((((uMat u - 1) * uMat m) * (uMat m - 1)ᴴ).trace).re = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      htr _ hX _ hY, Complex.zero_re]
  have hh : Formalism.REAL.hs (uMat m - 1) ≤ Formalism.REAL.hs (uMat (u * m) - 1) := by
    rw [e, hs_add, key]
    linarith [hs_nonneg ((uMat u - 1) * uMat m)]
  exact Real.sqrt_le_sqrt hh

theorem near : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k : Formalism.REAL.UJ ε, nrm (uMat (u * m * k) - 1) ≤ ρ → nrm (uMat k - 1) < ρ → nrm (uMat u - 1) < t ∧ nrm (uMat m - 1) < t ∧ nrm (uMat k - 1) < t := by
  intro n ε a j W hW t ht
  obtain ⟨ρ, hρ0, hρ1, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧ ρ ≤ t / 10 :=
    ⟨min (1 / 3) (t / 10), lt_min (by norm_num) (by linarith), min_le_left _ _, min_le_right _ _⟩
  refine ⟨ρ, hρ0, ?_⟩
  intro u hu m hm k hx hk
  have hK0 := nrm_nonneg (uMat k - 1)

  have hA : nrm (uMat (u * m) - 1) ≤ ρ * ρ + 2 * ρ := by
    have h := nrm_mul_sub_one (u * m * k) k⁻¹
    rw [mul_inv_cancel_right, nrm_inv] at h
    have : nrm (uMat (u * m * k) - 1) * nrm (uMat k - 1) ≤ ρ * ρ := mul_le_mul hx hk.le hK0 hρ0.le
    linarith

  have hM : nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := nrm_levi_le hW hu hm
  have hM0 := nrm_nonneg (uMat m - 1)
  have hU : nrm (uMat u - 1) ≤
      nrm (uMat (u * m) - 1) * nrm (uMat m - 1) + nrm (uMat (u * m) - 1) + nrm (uMat m - 1) := by
    have h := nrm_mul_sub_one (u * m) m⁻¹
    rwa [mul_inv_cancel_right, nrm_inv] at h
  have hρρ : ρ * ρ ≤ ρ / 3 := by nlinarith
  have hs0 : 0 ≤ ρ * ρ + 2 * ρ := by positivity
  have hs1 : ρ * ρ + 2 * ρ ≤ 1 := by linarith
  have hprod : nrm (uMat (u * m) - 1) * nrm (uMat m - 1) ≤ ρ * ρ + 2 * ρ :=
    calc _ ≤ (ρ * ρ + 2 * ρ) * (ρ * ρ + 2 * ρ) := mul_le_mul hA (hM.trans hA) hM0 hs0
      _ ≤ ρ * ρ + 2 * ρ := mul_le_of_le_one_left hs0 hs1
  exact ⟨by linarith, by linarith, by linarith⟩

end GlobalTheory.IwNear
end
