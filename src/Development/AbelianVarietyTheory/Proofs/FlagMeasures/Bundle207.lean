module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle179
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle065
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeHaarComplexGLInverse
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.momentPieriNumerics_of_sizeHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (U : ℕ → ℝ), (∀ i : Fin D.R.k, U (i.val + 1) = uS D w τ i) → Num D.R.k D.R.rS (lamD D τ) U (large₂.sc.b ^ max 2 Cu) (bOne D τ 1) ((D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) ((D.R.r : ℝ) ^ 19) (D.R.k * D.R.m ^ 5) ∧ GapCell D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) ∧ PI.BesselPeriodGGP.eps48 D.R.k D.R.rS = epsSH D.R := by
  first | exact @GlobalTheory.SizeNum.num_of_size | exact GlobalTheory.SizeNum.num_of_size | (intros; apply GlobalTheory.SizeNum.num_of_size <;> assumption)
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

theorem _root_.GlobalTheory.T.exists_besselCell_gap_constant : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  first | exact @GlobalTheory.GapConstant.gap_constant_exists | exact GlobalTheory.GapConstant.gap_constant_exists | (intros; apply GlobalTheory.GapConstant.gap_constant_exists <;> assumption)
end

section

open Matrix

noncomputable section
open Formalism.HermitianLatticeCounting.S6 Formalism.QuantumDeterminants GlobalTheory.DegVol.RealMat

namespace GlobalTheory.DegVol.FrameUnip

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {k r : ℕ} {σ : K →+* ℂ} {Φ : V → Fin (2 * r + k + 1) → ℂ}

theorem phi_zero' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) : Φ 0 = 0 := by
  have := h.2.1 0 0
  simpa using this

theorem phi_sub' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (x y : V) : Φ (x - y) = Φ x - Φ y := by
  have := h.1 (x - y) y
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem phi_sum' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {α : Type} (s : Finset α) (f : α → V) :
    Φ (∑ i ∈ s, f i) = ∑ i ∈ s, Φ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using phi_zero' h
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.1, ih]

theorem span_ind' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) (P : (Fin (2 * r + k + 1) → ℂ) → Prop) (h0 : ∀ x, P (Φ x))
    (ha : ∀ u v, P u → P v → P (u + v)) (hs : ∀ (c : ℂ) u, P u → P (c • u)) (u : Fin (2 * r + k + 1) → ℂ) : P u := by
  have hu : u ∈ Submodule.span ℂ (Set.range Φ) := by rw [h.2.2.2]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact h0 y
  | zero => rw [← phi_zero' h]; exact h0 0
  | add x y _ _ hx hy => exact ha _ _ hx hy
  | smul c x _ hx => exact hs _ _ hx

theorem mem_UH' (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (e : ∀ x y, herm (Hpk k r) (m *ᵥ Φ x) (m *ᵥ Φ y) = herm (Hpk k r) (Φ x) (Φ y)) : m ∈ UH (Hpk k r) := by
  have h1 : ∀ u w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w := by
    intro u
    refine span_ind' h (fun u => ∀ w, herm (Hpk k r) (m *ᵥ u) (m *ᵥ w) = herm (Hpk k r) u w) (fun x => ?_)
      (fun u v hu hv w => by rw [mulVec_add, herm_add_left, herm_add_left, hu, hv])
      (fun c u hu w => by rw [mulVec_smul, herm_smul_left, herm_smul_left, hu]) u
    exact span_ind' h _ (e x) (fun u v hu hv => by rw [mulVec_add, _root_.GlobalTheory.DegVol.RealMat.herm_add_right,
        _root_.GlobalTheory.DegVol.RealMat.herm_add_right, hu, hv])
      (fun c u hu => by rw [mulVec_smul, _root_.GlobalTheory.DegVol.RealMat.herm_smul_right,
        _root_.GlobalTheory.DegVol.RealMat.herm_smul_right, hu])
  ext i j
  exact (herm_bvec _ i j).symm.trans (by rw [← herm_mulVec, h1, herm_bvec])

theorem coord_span (h : GlobalTheory.DegVol.IsReal H k r σ Φ) {e : Fin r → V} {ρ : Fin r → ℂ}
    (he : ∀ a, Φ (e a) = ρ a • bvec (eI k r a)) {S : Set (Fin r)} (i : Fin (2 * r + k + 1))
    (hS : ∀ b ∈ S, b.val < i.val) {y : V} (hy : y ∈ Submodule.span K (e '' S)) : Φ y i = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hb' := hS b hb
    have : i ≠ eI k r b := fun e => by
      have := congrArg Fin.val e
      simp only [eI] at this; omega
    simp [he, bvec, this]
  | zero => rw [phi_zero' h]; rfl
  | add x y _ _ hx hy => rw [h.1, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [h.2.1, Pi.smul_apply, hx, smul_zero]

theorem mem_Nset : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {k r : ℕ} (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ),
    GlobalTheory.DegVol.IsReal H k r σ Φ → ∀ (e f : Fin r → V) (ρ ρ' : Fin r → ℂ), (∀ a, ρ a ≠ 0) → (∀ a, ρ' a ≠ 0) →
    (∀ a, Φ (e a) = ρ a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) →
    (∀ a, Φ (f a) = ρ' a • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    ∀ m : V →ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) →
    (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) →
    (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (∀ y, n *ᵥ Φ y = Φ (m y)) →
    n ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro K V _ _ _ _ H k r σ Φ h e f ρ ρ' hρ hρ' he hf hef m hm h2 h3 n hn
  refine ⟨mem_UH' h fun x y => by rw [hn, hn, h.2.2.1, h.2.2.1, hm], fun a i hi => ?_, fun i j hj hj' hi => ?_⟩
  · have := coord_span h he i (S := {b | b < a}) (fun b hb => lt_of_lt_of_le (Fin.lt_def.1 hb) hi) (h2 a)
    rw [phi_sub' h, ← hn, he, mulVec_smul, ← smul_sub, Pi.smul_apply, smul_eq_zero, or_iff_right (hρ a), Pi.sub_apply,
      sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this
  · let P : (Fin (2 * r + k + 1) → ℂ) → Fin (2 * r + k + 1) → ℂ := fun u =>
      u - ∑ a : Fin r, herm (Hpk k r) u (Φ (e a)) • Φ (f a)
    have hP : ∀ u, (n *ᵥ P u - P u) i = 0 := by
      refine span_ind' h _ (fun x => ?_) (fun u v hu hv => ?_) (fun c u hu => ?_)
      · have ex : P (Φ x) = Φ (x - ∑ a : Fin r, H.B x (e a) • f a) := by
          simp only [P, phi_sub' h, phi_sum' h, h.2.1, h.2.2.1]
        rw [ex, hn, ← phi_sub' h]
        have hperp : ∀ b, H.B (e b) (x - ∑ a : Fin r, H.B x (e a) • f a) = 0 := fun b => by

          rw [map_sub, map_sum]
          simp [hef]
          rw [starRingEnd_apply, H.herm, sub_self]
        have := h3 _ hperp
        rw [← Set.image_univ] at this
        exact coord_span h he i (fun b _ => lt_of_lt_of_le b.2 hi) this
      · have ex : P (u + v) = P u + P v := by
          simp only [P, herm_add_left, add_smul, Finset.sum_add_distrib]; abel
        rw [ex, mulVec_add, add_sub_add_comm, Pi.add_apply, hu, hv, add_zero]
      · have ex : P (c • u) = c • P u := by
          simp only [P, herm_smul_left, smul_sub, Finset.smul_sum, smul_smul]
        rw [ex, mulVec_smul, ← smul_sub, Pi.smul_apply, hu, smul_zero]
    have ex : P (bvec j) = bvec j := by
      simp only [P]
      rw [Finset.sum_eq_zero, sub_zero]
      intro a _
      have hne : esI k r a ≠ j := fun e' => by
        have := congrArg Fin.val e'
        have := a.2
        simp only [esI] at *; omega
      rw [he, herm_smul_right, herm_eI]
      simp [bvec, hne]
    have := hP (bvec j)
    rw [ex, Pi.sub_apply, sub_eq_zero] at this
    simpa [bvec, Pi.single_apply] using this

end GlobalTheory.DegVol.FrameUnip
end
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.MidLift

open GlobalTheory.DegVol.RealMat

variable {k r j : ℕ}

private lemma Hpk_esI_apply' (a : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) i = if i = eI k r a then 1 else 0 := by
  have ha := a.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, Hpk_esI_apply']

theorem coord_eq_zero {g : Mat k r} (hg : g ∈ UH (Hpk k r))
    (hX : ∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, a.val < j → herm (Hpk k r) u (g⁻¹ *ᵥ bvec (eI k r a)) = 0)
    (b : Fin r) (hb : b.val < j) : u (eI k r b) = 0 := by
  have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hg

  have hinj : Function.Injective (Matrix.mulVecLin g⁻¹) := by
    intro x y hxy
    have h := congrArg (fun v => g *ᵥ v) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] using h

  have hli : ∀ f : {a : Fin r // a.val < j} → Fin (2 * r + k + 1), Function.Injective f →
      LinearIndependent ℂ (fun a => bvec (f a)) := by
    intro f hf
    have h := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp f hf
    convert h using 1
    funext a
    simp [bvec, Function.comp]
  have hI1 : Function.Injective fun a : {a : Fin r // a.val < j} => eI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [eI, Fin.val_mk] at h'
    exact Subtype.ext (Fin.ext h')
  have hI2 : Function.Injective fun a : {a : Fin r // a.val < j} => esI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [esI, Fin.val_mk] at h'
    have := a.1.isLt
    have := a'.1.isLt
    exact Subtype.ext (Fin.ext (by omega))
  have hl1 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1)) := hli _ hI1
  have hl2 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hli _ hI2

  have hle : (XJ k r j).map (Matrix.mulVecLin g⁻¹) ≤ XstJ k r j := by
    unfold XJ
    rw [Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact (hX a.1 a.2).1
  have hrank : Module.finrank ℂ ((XJ k r j).map (Matrix.mulVecLin g⁻¹)) = Module.finrank ℂ (XstJ k r j) := by
    rw [← (Submodule.equivMapOfInjective _ hinj (XJ k r j)).finrank_eq]
    unfold XJ XstJ
    rw [finrank_span_eq_card hl1, finrank_span_eq_card hl2]
  have heq : (XJ k r j).map (Matrix.mulVecLin g⁻¹) = XstJ k r j :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : bvec (esI k r b) ∈ (XJ k r j).map (Matrix.mulVecLin g⁻¹) := by
    rw [heq]
    unfold XstJ
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
  have hzero : ∀ x ∈ XJ k r j, herm (Hpk k r) u (g⁻¹ *ᵥ x) = 0 := by
    intro x hx
    unfold XJ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hu a.1 a.2
    | zero => simp [herm]
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, h₁, h₂, add_zero]
    | smul c y _ h => rw [Matrix.mulVec_smul, GlobalTheory.DegVol.RealMat.herm_smul_right, h, mul_zero]
  rw [← herm_esI u b, ← hxe, Matrix.mulVecLin_apply]
  exact hzero x hx

theorem inWb_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF w hw
  unfold IsFrameOf at hF
  obtain ⟨hR, -, -, -, ⟨c, hN⟩, he, hist, -, -⟩ := hF
  unfold IsReal at hR
  obtain ⟨-, -, hiso, -⟩ := hR
  unfold IsNormal0 at hN
  obtain ⟨hgG, -, -, -, -, hX, -, -⟩ := hN
  unfold GlobalTheory.DegCnt.NF.Wn at hw
  rw [GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw

  have hBe : ∀ a : Fin r, H.B w (N.F.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F.e a.castSucc) w, hw _ h1, star_zero]
  have hBe' : ∀ a : Fin r, H.B w (N.F'.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F'.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F'.e a.castSucc) w, hw _ h1, star_zero]
  have hBist : ∀ b : Fin r, N.j ≤ b.val → H.B w (N.ist b) = 0 := by
    intro b hb
    have h1 : N.ist b ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← H.herm (N.ist b) w, hw _ h1, star_zero]
  have hρ' : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (pow_pos hρ n).ne'

  have hes : ∀ a : Fin r, Φ w (esI k r a) = 0 := by
    intro a
    have h1 := hiso w (N.F.e a.castSucc)
    rw [(he a).1, GlobalTheory.DegVol.RealMat.herm_smul_right, GlobalTheory.DegVol.RealMat.herm_eI, hBe a, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 (hρ' _))

  have hhi : ∀ b : Fin r, N.j ≤ b.val → Φ w (eI k r b) = 0 := by
    intro b hb
    have h1 := hiso w (N.ist b)
    rw [hist b hb, GlobalTheory.DegVol.RealMat.herm_smul_right, herm_esI, hBist b hb, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (star_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_pos hρ _).ne')))

  have hlo : ∀ b : Fin r, b.val < N.j → Φ w (eI k r b) = 0 := by
    have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hgG
    intro b hb
    refine coord_eq_zero (j := N.j) hgG hX (fun a _ => ?_) b hb
    have h3 : Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • (g⁻¹ *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_smul, ← (he a).2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    have h2 : g⁻¹ *ᵥ bvec (eI k r a) = (((ρ ^ (r - a.val) : ℝ) : ℂ))⁻¹ • Φ (N.F'.e a.castSucc) := by
      rw [h3, inv_smul_smul₀ (hρ' _)]
    rw [h2, GlobalTheory.DegVol.RealMat.herm_smul_right, hiso, hBe' a, map_zero, mul_zero]
  unfold inWb
  intro i hi
  rcases hi with hi | hi
  · have hb : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [← hb]
    by_cases hj : i.val < N.j
    · exact hlo ⟨i.val, hi⟩ hj
    · exact hhi ⟨i.val, hi⟩ (not_lt.1 hj)
  · have hlt : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have hb : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI, Fin.val_mk]
      have := i.isLt
      omega
    rw [← hb]
    exact hes _

end GlobalTheory.DegVol.MidLift
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameMass

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [TopologicalSpace E] in
theorem rmul_comp {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hf_sum_right (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm y (∑ i, c i • x i) = ∑ i, L.cj (c i) * hf L Hm y (x i) := by

  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gram_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, hf_sum_right, Matrix.mul_apply, cT,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) :
    (cT L A).det = L.cj A.det := by
  have h : cT L A = (L.cj.toRingEquiv.toRingHom.mapMatrix A).transpose := by
    ext i j; rfl
  rw [h, Matrix.det_transpose, ← RingHom.map_det]
  rfl

omit [TopologicalSpace E] in
theorem span_rmul {n m : ℕ} (x : Fin m → Fin n → E) (B : Matrix (Fin m) (Fin m) E)
    (hB : IsUnit B.det) :
    Submodule.span E (Set.range x) ≤ Submodule.span E (Set.range (rmul x B)) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h : rmul (rmul x B) B⁻¹ = x := by
    rw [rmul_comp, Matrix.mul_nonsing_inv _ hB]
    funext j
    simp [rmul, Matrix.one_apply]
  have h2 : x j = ∑ i, B⁻¹ i j • rmul x B i := (congrFun h j).symm
  rw [SetLike.mem_coe, h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

theorem mass_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 2 * r + 6 ≤ k → (∃ Λ, IsSD L S.Hm Λ) → ∃ κ : ℝ, 0 < κ ∧ ∀ C, S.IsCls C → ∀ p ∈ C, ∀ Mh : Submodule L.O S.V, S.Mof p.1 p.2 ≤ Mh → (∀ x ∈ Mh, x ∈ S.ME) → (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) → ENNReal.ofReal (κ / 2 * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) ≤ S.massSig Mh ∧ S.massSig Mh ≤ ENNReal.ofReal (2 * κ * (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hk ⟨Λs, hΛs⟩
  obtain ⟨x, hx, hME, -, hlat, hmass, hcls⟩ := GlobalTheory.HL.FrameTuple.main L r k S
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDual_hermitianLattice_mass_bounds L S.ϖ S.ϖ_irr S.Hm S.herm Λs hΛs (2 * r + 2) x hx
    (by omega) _ hlat
  refine ⟨κ, hκ, fun C hC p hp Mh hle hin hint => ?_⟩
  obtain ⟨y, B, hB, hy, hM⟩ := hcls C hC p hp
  have hBu : IsUnit B.det := IsUnit.of_mul_eq_one _ hB
  have hBc : IsUnit (L.cj B.det) := hBu.map L.cj
  have hyu : IsUnit (gramT L S.Hm y).det := by
    rw [hy, gram_rmul, Matrix.det_mul, Matrix.det_mul, det_cT]
    exact (hBc.mul hx).mul hBu
  obtain ⟨-, A, hAi, hAu, hMh, hli, hA⟩ := GlobalTheory.HL.OverBasis.exists_basis_overlattice L S.Hm S.herm
    (2 * r + 2) y hyu Mh (hM ▸ hle)
    (fun v hv => by rw [hy]; exact span_rmul x B hBu (hME ▸ hin v hv)) hint
  obtain ⟨hv, hidx⟩ := GlobalTheory.MatrixIndex.index_rmul L S.ϖ S.ϖ_irr _ hli A hAi hAu
  rw [hA, ← hM, ← hMh] at hidx
  have hinv : (A * B⁻¹)⁻¹ = B * A⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hBu]
  have hr : rmul x (A * B⁻¹)⁻¹ = rmul y A⁻¹ := by rw [hinv, hy, rmul_comp]
  have hBB : B⁻¹.det * B.det = 1 := Matrix.det_nonsing_inv_mul_det _ hBu
  have hdet : (A * B⁻¹).det * L.cj (A * B⁻¹).det = A.det * L.cj A.det := by
    have h1 : L.cj B⁻¹.det * L.cj B.det = 1 := by rw [← map_mul, hBB, map_one]
    rw [Matrix.det_mul, map_mul]
    linear_combination (-(A.det * L.cj A.det * B⁻¹.det * L.cj B⁻¹.det)) * hB
      + (A.det * L.cj A.det * L.cj B⁻¹.det * L.cj B.det) * hBB + (A.det * L.cj A.det) * h1
  have hu : IsUnit (A * B⁻¹).det := by
    rw [Matrix.det_mul]; exact hAu.mul (IsUnit.of_mul_eq_one _ hBB)
  have hI : IsIntM L (gramT L S.Hm (rmul x (A * B⁻¹)⁻¹)) := by
    rw [hr]
    intro a b
    refine hint _ ?_ _ ?_ <;> rw [hMh] <;> exact Submodule.subset_span ⟨_, rfl⟩
  have key := hU (A * B⁻¹) hu hI
  rw [hr, ← hMh, hdet, hME, ← hmass] at key
  have hpow : (resQ S.ϖ : ℝ) ^ (-(vE L S.ϖ (A.det * L.cj A.det) *
        (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)))) =
      (((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup : ℝ) ^ (k - 1))⁻¹ := by
    rw [hidx, zpow_neg]
    congr 1
    have e : (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ)) = ((k - 1 : ℕ) : ℤ) := by omega
    rw [e]
    conv_lhs => rw [← Int.toNat_of_nonneg hv]
    rw [← Nat.cast_mul, zpow_natCast, pow_mul]
    push_cast
    rfl
  rw [hpow] at key
  exact key

end GlobalTheory.HL.FrameMass
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.hasEuclideanBallVolume_haarComplexGL_inverse : ∀ j : ℕ, IsRadial (ENNReal.ofReal (2 ^ (j ^ 2)) • haarLoc j) (fun x => Formalism.REAL.hs (Matrix.of x - 1) + Formalism.REAL.hs ((Matrix.of x)⁻¹ - 1)) (2 * j ^ 2) := by
  first | exact @GlobalTheory.LeviIso.isRadial_haarLoc | exact GlobalTheory.LeviIso.isRadial_haarLoc | (intros; apply GlobalTheory.LeviIso.isRadial_haarLoc <;> assumption)
end
