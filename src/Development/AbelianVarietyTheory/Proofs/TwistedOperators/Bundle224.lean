module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMatrixOfIsLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle022
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle216
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open Classical MeasureTheory

theorem _root_.GlobalTheory.T.average_det_char_monomial_eq_sum_prod_minors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (m : ι → ℤ), ∃ n : ι → ℕ,
  ∀ {K : Type} [Group K] [MeasurableSpace K] (ν : Measure K), IsProbabilityMeasure ν → ν.IsMulLeftInvariant →
  (∀ g0 : K, AEMeasurable (g0 * ·) ν) →
  ∀ (ρ : K →* (ι → Matrix.unitaryGroup (Fin a) ℂ)), (∀ τ i j, Measurable fun g => (ρ g τ : Matrix (Fin a) (Fin a) ℂ) i j) → Function.Surjective ρ →
  ∀ (Λ : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] ℂ) (k : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
  ∃ (M : ℕ) (r : Fin M → ℂ) (U : Fin M → GlobalTheory.MinorFrame.Tup ι a d n), (∀ p, IsAlgebraic ℚ (r p)) ∧
    ∫ g, (∏ τ, (ρ g τ : Matrix (Fin a) (Fin a) ℂ).det ^ (m τ)) *
      Λ (GlobalTheory.MinorFrame.colSub (fun τ => (ρ g τ : Matrix (Fin a) (Fin a) ℂ)) (MvPolynomial.monomial k 1)) ∂ν =
    ∑ p, r p * Λ (GlobalTheory.MinorFrame.prodMinors (U p)) := by
  first | exact @GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors | exact GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors | (intros; apply GlobalTheory.MinorFrame.AvgCore.average_monomial_eq_sum_prodMinors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
open IsDedekindDomain Formalism.L2.NTheta
open scoped Matrix

namespace GlobalTheory.HatLocalChart

open scoped TensorProduct

theorem smul_mem_hat (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    a • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction ha using AddSubgroup.closure_induction with
  | mem a' ha' =>
    obtain ⟨b, hb, x, rfl⟩ := ha'
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, w, hw, rfl⟩ := hz
      apply AddSubgroup.subset_closure
      refine ⟨b * c, fun v => ?_, x • w, L.smul_mem x hw, ?_⟩
      · have hbv := hb v
        simp only [Formalism.MainNotions.StandardLattice.intAf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV, Set.mem_setOf_eq] at hbv
        exact mul_mem hbv (hc v)
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
    | zero => rw [smul_zero]; exact zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
    | neg y _ h => rw [smul_neg]; exact neg_mem h
  | zero => rw [zero_smul]; exact zero_mem _
  | add a₁ a₂ _ _ h₁ h₂ => rw [add_smul]; exact add_mem h₁ h₂
  | neg a _ h => rw [neg_smul]; exact neg_mem h



theorem exists_chart : ∀ (D : D7) (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (π : GlobalTheory.SplitPlace.RF D →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v → AE D) (n : ℕ)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), e * e = e →
    (∀ a, π (finPart D (s a)) = a) → (∀ x, finPart D (s (π x)) = finPart D e * x) →
    (∀ x, finPart D e * x ∈ intAE D ↔ π x ∈ Formalism.UG.Ov D.host.F v) →
    L.FG → Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ →
    ∃ C : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v), ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔
        ∀ i, ((C⁻¹ : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)).1 *ᵥ fun j => π (y j)) i ∈ Formalism.UG.Ov D.host.F v := by
  intro D e v π s n L he h1 h2 h3 hfg hspan
  have hπ1 : π (finPart D e) = 1 := by
    have h := h2 1
    rw [map_one, mul_one] at h
    rw [← h, h1 1]
  have heint : finPart D e ∈ intAE D := by
    have h := (h3 1).2 (by rw [map_one]; exact one_mem _)
    rwa [mul_one] at h
  have hπint : ∀ x ∈ intAE D, π x ∈ Formalism.UG.Ov D.host.F v := fun x hx =>
    (h3 x).1 (GlobalTheory.SplitLatBasis.mul_mem_intAE D heint hx)
  have hone : ∀ w : HeightOneSpectrum (𝓞 D.host.F),
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) w ∈ w.adicCompletionIntegers D.host.F :=
    fun w => one_mem (w.adicCompletionIntegers D.host.F)
  obtain ⟨g, hg⟩ := hfg
  let O := v.adicCompletionIntegers D.host.F
  let gen : ↥(g : Set (Fin n → D.host.E)) → Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E :=
    fun j i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (j : Fin n → D.host.E) i
  let N : Submodule O (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) :=
    Submodule.span O (Set.range fun j i => π (gen j i))

  have hL : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, (∀ w, a w ∈ w.adicCompletionIntegers D.host.F) →
      ∀ x ∈ L, (fun i => π (a ⊗ₜ[D.host.F] x i)) ∈ N := by
    intro a ha x hx
    have haE : a ⊗ₜ[D.host.F] (1 : D.host.E) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨a, fun w => ha w, 1, by simp⟩
    rw [← hg] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hx' : (fun i => π (a ⊗ₜ[D.host.F] x i)) =
          (⟨π (a ⊗ₜ[D.host.F] (1 : D.host.E)), hπint _ haE⟩ : O) • (fun i => π (gen ⟨x, hx⟩ i)) := by
        funext i
        show π (a ⊗ₜ[D.host.F] x i) = π (a ⊗ₜ[D.host.F] (1 : D.host.E)) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hx']
      exact N.smul_mem _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
    | zero =>
      convert N.zero_mem using 1 <;> ext i <;> simp
    | add x y _ _ hx hy =>
      convert N.add_mem hx hy using 1
      funext i
      simp [TensorProduct.tmul_add]
    | smul c x _ hx =>
      have hc : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩
      convert N.smul_mem (⟨π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)), hπint _ hc⟩ : O) hx using 1
      funext i
      show π (a ⊗ₜ[D.host.F] ((c : D.host.E) * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E)) * π (a ⊗ₜ[D.host.F] x i)
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hz : ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)), (fun i => π (z i)) ∈ N := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact hL a ha x hx
    | zero =>
      convert N.zero_mem using 1 <;> ext i <;> simp
    | add z₁ z₂ _ _ h₁ h₂ =>
      convert N.add_mem h₁ h₂ using 1 <;> ext i <;> simp
    | neg z _ h =>
      convert N.neg_mem h using 1 <;> ext i <;> simp
  have hgen : ∀ j, gen j ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := fun j =>
    AddSubgroup.subset_closure ⟨1, hone, j, hg ▸ Submodule.subset_span j.2, rfl⟩
  have hiff : ∀ y : Fin n → GlobalTheory.SplitPlace.RF D,
      finPart D e • y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) ↔ (fun j => π (y j)) ∈ N := by
    intro y
    constructor
    · intro hy
      convert hz _ hy using 1
      funext j
      show π (y j) = π (finPart D e * y j)
      rw [map_mul, hπ1, one_mul]
    · intro hy
      have hs := GlobalTheory.SplitLatBasis.section_mem O π (fun a => finPart D (s a)) (finPart D e) (intAE D)
        (GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) h1 h2 (fun x hx => (h3 x).2 hx)
        (fun a ha y hy => smul_mem_hat D L ha hy) gen hgen _ hy
      convert hs using 1
      funext j
      exact (h2 (y j)).symm
  have hfin : N.FG := Submodule.fg_span (Set.finite_range _)
  have htop : Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)
      (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v)) = ⊤ := by
    set S := Submodule.span (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) (N : Set (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v))
    have hΦ : ∀ x ∈ Submodule.span D.host.E (L : Set (Fin n → D.host.E)),
        (fun i => π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)) ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (hL 1 hone x hx)
      | zero =>
        convert S.zero_mem using 1 <;> ext i <;> simp
      | add x y _ _ hx hy =>
        convert S.add_mem hx hy using 1
        funext i
        simp [TensorProduct.tmul_add]
      | smul c x _ hx =>
        convert S.smul_mem (π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c)) hx using 1
        funext i
        show π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (c * x i)) = π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] c) * π ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] x i)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [Submodule.eq_top_iff']
    intro w
    rw [pi_eq_sum_univ w]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    convert hΦ (fun j => if i = j then 1 else 0) (by rw [hspan]; trivial) using 1
    funext j
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [TensorProduct.tmul_zero, map_zero]
  haveI : Submodule.IsLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := Submodule.IsLattice.of_fg _ hfin
  haveI : Submodule.IsFullLattice (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) N := ⟨htop⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_matrix_of_isLattice (R := O) N
  refine ⟨B, fun y => (hiff y).trans ((hB _).trans (forall_congr' fun i => ?_))⟩
  constructor
  · rintro ⟨r, hr⟩
    rw [← hr]
    exact r.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

end GlobalTheory.HatLocalChart
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeOffParts
open scoped Matrix

theorem mulVec_one_sub_idempotent_of_split_sum_identity {A : Type} [CommRing A] {n : ℕ} (a b : A) (h1 : a * a = a) (h2 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) A) (z : Fin n → A) (h6 : M *ᵥ z = (a + b) • M *ᵥ z + z - (a + b) • z) :
    M *ᵥ ((1 - a) • z) = b • M *ᵥ z + z - a • z - b • z := by
  have hP : (1 - a) * (a + b) = b := by linear_combination -h1 - h2
  rw [Matrix.mulVec_smul]
  conv_lhs => rw [h6]
  rw [smul_sub, smul_add, smul_smul, smul_smul, hP, sub_smul, one_smul]
  abel

open GlobalTheory.SplitPlace in
theorem inv_part_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ z ∈ Formalism.L2.NTheta.LamHat V,
      fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z) ∈ Formalism.L2.NTheta.LamHat V := by
  intro z hz
  obtain ⟨-, hs, h3, -⟩ := ha
  have hi := idem_mem he.1
  have hci := cf_mem hi
  have h3' : ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D e • fm V a₀ *ᵥ y ∈ Formalism.L2.NTheta.LamHat V := h3
  have hadj := adj_mem V (finPart D e) a₀ h3' z hz
  have h6 := mulVec_parts (finPart D) ((suppAt_iff e V a₀⁻¹).1 (suppAt_inv hs)) z
  rw [RingHom.map_add (f := _), fin_cA, ← fm_eq] at h6
  have e1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have e2 : finPart D e * cf D (finPart D e) = 0 := by rw [← fin_cA, ← map_mul, he.2.1, map_zero]
  rw [mulVec_one_sub_idempotent_of_split_sum_identity _ _ e1 e2 _ z h6]
  have m1 : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hi hz
  have m2 : cf D (finPart D e) • z ∈ Formalism.L2.NTheta.LamHat V := smul_mem V hci hz
  have m3 := (Formalism.L2.NTheta.LamHat V).add_mem hadj hz
  have m4 := (Formalism.L2.NTheta.LamHat V).sub_mem m3 m1
  exact (Formalism.L2.NTheta.LamHat V).sub_mem m4 m2

open GlobalTheory.SplitPlace in
theorem hat_one_mem {D : D7} {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {ϖ : D.host.E} {k : ℕ} {a₀ : GA D V}
    (ha : Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀) :
    ∀ w ∈ latGHat V 1, fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • w) ∈ latGHat V 1 := by
  intro w hw
  let f : (Fin V.rank → RF D) →+ (Fin V.rank → RF D) :=
    (Matrix.mulVecLin (fm V a₀⁻¹)).toAddMonoidHom.comp (DistribSMul.toAddMonoidHom _ (1 - finPart D e))
  change f w ∈ latGHat V 1
  unfold latGHat at hw ⊢
  refine AddSubgroup.mem_comap.1 ((AddSubgroup.closure_le (K := AddSubgroup.comap f _)).2 ?_ hw)
  rintro _ ⟨a, haA, x, ⟨x', hx', rfl⟩, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  refine AddSubgroup.subset_closure ⟨a, haA, _, ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'), ?_, rfl⟩, ?_⟩
  · have hx'' : x' ∈ Formalism.L2.NTheta.LamHat V := by
      rw [← GlobalTheory.LatReflection.latHat_eq_lamHat]; exact hx'
    have := inv_part_mem he ha x' hx''
    rw [← GlobalTheory.LatReflection.latHat_eq_lamHat] at this
    exact this
  · simp only [map_one, Units.val_one, Matrix.one_mulVec]
    change fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • (((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • x')) =
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] a) • (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • x'))
    rw [smul_comm (1 - finPart D e), Matrix.mulVec_smul]

open GlobalTheory.SplitPlace in
theorem off_parts : ∀ (D : D7) (V : HSp D) (e : AE D) (ϖ : D.host.E) (k : ℕ) (g a₀ : GA D V),
    Formalism.L2.Theta.IsSplitIdem D e → Formalism.L2.NTheta.IsHeckeElt V e ϖ k a₀ →
    ∀ y ∈ latGHat V g, (1 - finPart D e) • y ∈ latGHat V (g * a₀) := by
  intro D V e ϖ k g a₀ he ha y hy
  obtain ⟨z, hz, rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g).2 y).1 hy
  refine ((GlobalTheory.MarkCoset.latG_spec D V (g * a₀)).2 _).2
    ⟨fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z), hat_one_mem he ha z hz, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  change (finHom V g).1 *ᵥ (fm V a₀ *ᵥ (fm V a₀⁻¹ *ᵥ ((1 - finPart D e) • z))) = _
  rw [fm_vec_inv, Matrix.mulVec_smul]

end GlobalTheory.HeckeOffParts
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar




namespace GlobalTheory.PhaseReal

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j
  rfl

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i

theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem hO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    hO V W (isoPart V W C κ) (isoPart V W C' (y.map (incA D))) =
      Matrix.trace ((adj D y * W.gram).map (incA D) * κ) := by
  have hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y := by
    rw [conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    rw [Matrix.map_mul]
    rfl
  have hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D) := by
    rw [hu, ← hz]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.cA_incA _
  have e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) =
      C'.map (incA D) * (adj D y * W.gram).map (incA D) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit,
      Matrix.mul_assoc]
  have e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D) := rfl
  rw [hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2,
    Matrix.mul_one]

theorem pairQ_map (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (pairQ W y).map (incA D) = incA D D.host.xi0 • (adj D y * W.gram).map (incA D) := by
  ext i j
  simp only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem symplO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    symplO V W (isoPart V W C' (y.map (incA D))) (isoPart V W C κ) =
      -Algebra.trace (AF D.host.F) (AE D) (Matrix.trace ((pairQ W y).map (incA D) * κ)) := by
  unfold symplO
  rw [← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem finPart_trace {m n : ℕ} (P : Matrix (Fin n) (Fin m) (AE D)) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) : finPart D (Matrix.trace (P * κ)) = 0 := by
  have h : ∀ i j, finPart D (κ i j) = 0 := fun i j => congrFun (congrFun hκ i) j

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem trace_real {t : AE D} (h : finPart D t = 0) :
    Algebra.trace (AF D.host.F) (AE D) t =
      pairA D.host.F (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t)) 0 := by
  have h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t =
      Algebra.trace (AF D.host.F) (AE D) t := by
    conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]
  refine Prod.ext rfl ?_
  have := congrArg Prod.snd h3
  exact this.symm.trans (zero_mul _)

theorem theta_trace (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : AE D) :
    θ ρ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) := by
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t :=
    GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t
  have hB := congrArg (infPart D) hA
  rw [map_add (f := _), infPart_cA] at hB
  have hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) =
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [← hC, hB, map_add (f := _), GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]

theorem theta_pair (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) D.host.E) (κ : Mx D m n) :
    θ ρ (infPart D (Matrix.trace (P.map (incA D) * κ))) =
      Matrix.trace (P.map (tauE D ρ) * compAt θ ρ κ) := by
  have h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hθ ρ).1 e

  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]

end GlobalTheory.PhaseReal

theorem GlobalTheory.PhaseReal.phase_eq : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  intro D V W r C C' hC ψ hψ θ hθ y κ hκ
  unfold phase
  rw [GlobalTheory.PhaseReal.symplO_iso V W C C' hC]
  set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F T))
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht,
      GlobalTheory.PhaseReal.theta_pair θ hθ ρ]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  first | exact @GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | exact GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | (intros; apply GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one <;> assumption)
end
