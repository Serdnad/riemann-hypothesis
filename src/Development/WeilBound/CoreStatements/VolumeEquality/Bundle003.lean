module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle120
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle043
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

def HasRk (H : Host E) (p q : ℕ) {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : Prop :=
  ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp R.B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then p else q

theorem label_conj (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inr τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inl τ))) := by
  refine RingHom.ext fun a => ?_
  let ψ : E →+* ℂ := κ.comp (τ.1.codRestrict c.F (c.conj τ.1))
  show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem label_conj' (κ : c.F →+* ℂ) (τ : CMType H) :
    κ.comp (labelEmb c (.inl τ)) = (starRingEnd ℂ).comp (κ.comp (labelEmb c (.inr τ))) := by
  rw [label_conj]
  exact RingHom.ext fun a => by simp

theorem label_bij (κ : c.F →+* ℂ) : Function.Bijective fun lab : CMType H ⊕ CMType H => κ.comp (labelEmb c lab) :=
  LabPt.bijective_of_injective H _ (FamEx.labelEmb_comp_injective E H l c κ)

theorem label_cm (κ : c.F →+* ℂ) :
    IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inl τ))) ∧ IsCMFam (fun τ : CMType H => κ.comp (labelEmb c (.inr τ))) := by
  refine LabPt.isCMFam_of_bijective _ _ ?_ (label_conj κ)
  convert label_bij (c := c) κ using 1
  funext s
  rcases s with τ | τ <;> rfl

theorem hasRk_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    HasRk H p q R ↔ ∀ τ : CMType H, Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inl τ)))) = p ∧
      Module.finrank ℂ (eigSp R.B (κ.comp (labelEmb c (.inr τ)))) = q := by
  have hne : -H.rt0 ≠ H.rt0 := fun e => FamEx.rt0_ne_zero H (by linear_combination (-1/2 : ℂ) * e)
  constructor
  · intro h τ
    obtain ⟨s, hs, hv⟩ := FamEx.exists_emb_label E H l c κ (.inl τ)
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ (.inr τ)
    have e := hv ρ hρ
    have e' := hv' ρ hρ
    simp only [Sum.elim_inl, Sum.elim_inr, hκ] at e e'
    rw [hs, hs', h s, h s', if_pos e, if_neg (by rw [e']; exact hne)]
    exact ⟨rfl, rfl⟩
  · intro h s
    obtain ⟨lab, hl⟩ := (label_bij (c := c) κ).2 (s.comp (algebraMap (𝓞 E) E))
    obtain ⟨s', hs', hv'⟩ := FamEx.exists_emb_label E H l c κ lab
    have e := hv' ρ hρ
    have hl' : κ.comp (labelEmb c lab) = s.comp (algebraMap (𝓞 E) E) := hl
    have e2 : s (H.rt : E) = s' (H.rt : E) := RingHom.congr_fun (hl'.symm.trans hs') H.rt
    rw [← hl', e2, e]
    rcases lab with τ | τ
    · simp only [Sum.elim_inl, hκ, if_true]
      exact (h τ).1
    · simp only [Sum.elim_inr, hκ, if_neg hne]
      exact (h τ).2

theorem hasSig_iff (κ : c.F →+* ℂ) (ρ : c.F) (hρ : (ρ : ℂ) = H.rt0) (hκ : κ ρ = H.rt0) (p q : ℕ)
    (sm : CMType H → CMType H ⊕ CMType H) (j j' : ℕ)
    (hs : sm = Sum.inr ∧ j = p ∧ j' = q ∨ sm = Sum.inl ∧ j = q ∧ j' = p) {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) :
    R.HasSig (fun τ => κ.comp (labelEmb c (sm τ))) j j' ↔ HasRk H p q R := by
  rw [hasRk_iff κ ρ hρ hκ]
  refine forall_congr' fun τ => ?_
  rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rw [label_conj' κ τ]
    exact and_comm
  · rw [label_conj κ τ]

theorem side_cm (κ : c.F →+* ℂ) (sm : CMType H → CMType H ⊕ CMType H) (hs : sm = Sum.inr ∨ sm = Sum.inl) :
    IsCMFam fun τ => κ.comp (labelEmb c (sm τ)) := by
  rcases hs with rfl | rfl
  · exact (label_cm κ).2
  · exact (label_cm κ).1

end SheetDecomposition
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace SheetDecomposition.Univ

theorem imH_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    ((z + z') ⬝ᵥ M *ᵥ star w).im = (z ⬝ᵥ M *ᵥ star w).im + (z' ⬝ᵥ M *ᵥ star w).im := by
  rw [add_dotProduct, Complex.add_im]

theorem imH_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    ((r • z) ⬝ᵥ M *ᵥ star w).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  rw [smul_dotProduct, Complex.smul_im, smul_eq_mul]

theorem imH_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (w + w')).im = (z ⬝ᵥ M *ᵥ star w).im + (z ⬝ᵥ M *ᵥ star w').im := by
  rw [star_add, mulVec_add, dotProduct_add, Complex.add_im]

theorem imH_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z w : Fin g → ℂ) :
    (z ⬝ᵥ M *ᵥ star (r • w)).im = r * (z ⬝ᵥ M *ᵥ star w).im := by
  have h : star (r • w) = (r : ℂ) • star w := by
    ext i
    simp
  rw [h, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]

theorem exists_realExt {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (hf : R'.form = R.form) :
    ∃ L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), (∀ x, L (R.P x) = R'.P x) ∧
      (∀ z w, (L z ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (z ⬝ᵥ R.Hm *ᵥ star w).im) ∧
      ∀ a z, L (R.B a z) = R'.B a (L z) := by
  classical
  haveI := R.free
  haveI := R.fin
  have hspan : Submodule.span ℝ (Set.range R.P) = ⊤ := (SheetDecomposition.riemBasic E g Λ Unit R).2.1
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ R.rank
  let v : Fin (2 * g) → Fin g → ℂ := fun k => R.P (b k)
  have hsum : ∀ (Q : Λ →+ (Fin g → ℂ)) (x : Λ), Q x = ∑ k, (b.repr x k : ℝ) • Q (b k) := by
    intro Q x

    conv_lhs => rw [← b.sum_repr x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have hv : (⊤ : Submodule ℝ (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [hsum R.P x]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  let c : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ) := basisOfTopLeSpanOfCardEqFinrank v hv hcard
  have hc : ∀ k, c k = R.P (b k) := fun k => by
    simp [c, v, coe_basisOfTopLeSpanOfCardEqFinrank]
  let L : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := c.constr ℝ fun k => R'.P (b k)
  have hLb : ∀ k, L (R.P (b k)) = R'.P (b k) := fun k => by
    rw [← hc k]
    exact c.constr_basis ℝ _ k
  have hL : ∀ x, L (R.P x) = R'.P x := by
    intro x

    rw [hsum R.P x, hsum R'.P x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hLb]
  have hall : ∀ z : Fin g → ℂ, z ∈ Submodule.span ℝ (Set.range R.P) := fun z => hspan ▸ Submodule.mem_top
  refine ⟨L, hL, ?_, ?_⟩
  · have h1 : ∀ (x : Λ) (w : Fin g → ℂ),
        (L (R.P x) ⬝ᵥ R'.Hm *ᵥ star (L w)).im = (R.P x ⬝ᵥ R.Hm *ᵥ star w).im := by
      intro x w
      induction hall w using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨y, rfl⟩ := hw
        rw [hL, hL, R'.im, R.im, hf]
      | zero => simp
      | add w w' _ _ h h' => rw [map_add (f := _), imH_add_right, imH_add_right, h, h']
      | smul r w _ h => rw [map_smul, imH_smul_right, imH_smul_right, h]
    intro z w
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      exact h1 x w
    | zero => simp
    | add z z' _ _ h h' => rw [map_add (f := _), imH_add_left, imH_add_left, h, h']
    | smul r z _ h => rw [map_smul, imH_smul_left, imH_smul_left, h]
  · intro a z
    induction hall z using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      rw [← R.act, hL, hL, R'.act]
    | zero => simp
    | add z z' _ _ h h' => simp only [map_add (f := _), h, h']
    | smul r z _ h =>
      rw [LinearMap.map_smul_of_tower, map_smul, h, map_smul, LinearMap.map_smul_of_tower]

end SheetDecomposition.Univ
end
end
