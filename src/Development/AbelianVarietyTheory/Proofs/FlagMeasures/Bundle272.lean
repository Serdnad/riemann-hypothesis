module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle261
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle262
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle203
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitive
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle264
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021

@[expose] public section

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.Cov

theorem covol_of_act {G α : Type} [Group G] [MeasurableSpace α] (act : G → α → α) (h1 : ∀ x, act 1 x = x)
    (h2 : ∀ s t x, act (s * t) x = act s (act t x)) (μ : Measure α) (R : Set α) (A B : Subgroup G) (Ω K : Set α)
    (hm : ∀ s, Measurable (act s)) (cA : Countable A) (cB : Countable B) (hR : μ Rᶜ = 0)
    (hinv : ∀ s ∈ A ⊔ B, (∀ x ∈ R, act s x ∈ R) ∧ μ.map (act s) = μ) (hAB : A.relIndex B ≠ 0) (hBA : B.relIndex A ≠ 0)
    (hΩ : MeasurableSet Ω) (hK : MeasurableSet K) (fA : ∀ x ∈ R, ∃! s, s ∈ A ∧ act s x ∈ Ω)
    (fB : ∀ x ∈ R, ∃! s, s ∈ B ∧ act s x ∈ K) : μ K = ENNReal.ofReal (GlobalTheory.HL.invVol A B) * μ Ω := by
  letI : MulAction G α := { smul := act, one_smul := h1, mul_smul := h2 }
  exact GlobalTheory.T.fundamental_set_measure_commensurable_index_ratio G α μ R A B Ω K hm cA cB hR hinv hAB hBA hΩ hK fA fB

theorem continuous_lmulM {k r : ℕ} (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  unfold lmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem rset_mul {k r : ℕ} {γ : Mat k r} (hu : IsUnit γ.det) {a b : Mat k r} (ha : a ∈ Rset k r γ) (hb : b ∈ Rset k r γ) :
    a * b ∈ Rset k r γ := by
  refine ⟨WeylGroupFacts.mem_n_mul ha.1 hb.1, ?_⟩
  have e : γ * (a * b) * γ⁻¹ = (γ * a * γ⁻¹) * (γ * b * γ⁻¹) := by
    have : (γ * a * γ⁻¹) * (γ * b * γ⁻¹) = γ * a * (γ⁻¹ * γ) * b * γ⁻¹ := by simp only [Matrix.mul_assoc]
    rw [this, nonsing_inv_mul _ hu, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e]
  exact WeylGroupFacts.mem_n_mul ha.2 hb.2

theorem countable_aut (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Countable (V ≃ₗ[K] V) := by
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  haveI : Countable V := (Module.finBasis K V).equivFun.injective.countable
  let b := Module.finBasis K V
  refine Function.Injective.countable (f := fun s : V ≃ₗ[K] V => fun i => s (b i)) fun s t e => ?_
  exact LinearEquiv.toLinearMap_injective (b.ext fun i => congrFun e i)

theorem cov_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N k ι _ σ β Φ z z' g hP hd hF hN hv gg Λ Kf hgg hT hKf
  obtain ⟨hex, hsep, hsub, -⟩ := RealMat.real_points K V H hK r N k ι σ β Φ z z' g hP hd hF
  have hι : Nonempty ι := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    exact ⟨(hP.2 w).choose⟩
  obtain ⟨v0⟩ := id hι
  choose m hm using fun s => (hex s).exists
  have hmu : ∀ (s : V ≃ₗ[K] V) (y : ι → Mt k r), (∀ v x, Matrix.of (y v) *ᵥ Φ v x = Φ v (s x)) → y = m s :=
    fun s y hy => (hex s).unique hy (hm s)
  have hH : ∀ v, IsHaarOn (Rset k r (g v)) (lebR0 k r N.j β) := fun v => by
    obtain ⟨-, hz, hz', hT0, ⟨c, hc⟩, -⟩ := hF v
    exact (GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r N.j N.j_le (z v) (z' v) (g v) β c hz hz' hT0 hc).1
  haveI : SigmaFinite (lebR0 k r N.j β) := (hH v0).1
  have hu : ∀ v, IsUnit (g v).det := fun v => RealMat.isUnit_det (hF v).2.2.2.2.1.choose_spec.1
  have hone : m 1 = fun _ => Matrix.of.symm (1 : Mat k r) :=
    (hmu 1 _ fun v x => by simp only [Equiv.apply_symm_apply, Matrix.one_mulVec]; rfl).symm
  have hmul : ∀ s t, m (s * t) = fun v => Matrix.of.symm (Matrix.of (m s v) * Matrix.of (m t v)) := fun s t =>
    (hmu (s * t) _ fun v x => by
      simp only [Equiv.apply_symm_apply]
      rw [← mulVec_mulVec, hm, hm]; rfl).symm
  have h1 : ∀ x : ι → Mt k r, mulP (m 1) x = x := fun x => by
    rw [hone]; funext v
    show (1 : Mat k r) * Matrix.of (x v) = x v
    rw [Matrix.one_mul]; rfl
  have h2 : ∀ s t (x : ι → Mt k r), mulP (m (s * t)) x = mulP (m s) (mulP (m t) x) := fun s t x => by
    rw [hmul]; funext v
    show (Matrix.of (m s v) * Matrix.of (m t v)) * Matrix.of (x v) = Matrix.of (m s v) * (Matrix.of (m t v) * Matrix.of (x v))
    rw [Matrix.mul_assoc]
  have hmeas : ∀ s, Measurable (mulP (k := k) (r := r) (m s)) := fun s =>
    Measurable.of_eval fun v => (continuous_lmulM _).measurable.comp (measurable_pi_apply v)
  have hmR : ∀ s ∈ N.R, m s ∈ RP k r g := fun s hs => hsub ⟨s, hs, hm s⟩
  have hnull : Measure.pi (fun _ : ι => lebR0 k r N.j β) (RP k r g)ᶜ = 0 := by
    refine measure_mono_null (t := ⋃ v, Function.eval v ⁻¹' {x : Mt k r | Matrix.of x ∉ Rset k r (g v)}) ?_
      (measure_iUnion_null fun v => Measure.pi_eval_preimage_null _ (hH v).2.2.1)
    intro x hx
    simp only [RP, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨v, hv'⟩ := hx
    exact Set.mem_iUnion.2 ⟨v, hv'⟩
  have hpres : ∀ s ∈ N.R, (Measure.pi fun _ : ι => lebR0 k r N.j β).map (mulP (m s)) =
      Measure.pi fun _ : ι => lebR0 k r N.j β := fun s hs => by
    have e : ∀ v, (lebR0 k r N.j β).map (lmulM (Matrix.of (m s v))) = lebR0 k r N.j β :=
      fun v => (hH v).2.2.2 _ (hmR s hs v)
    haveI : ∀ v, SigmaFinite ((lebR0 k r N.j β).map (lmulM (Matrix.of (m s v)))) := fun v => by rw [e]; infer_instance
    have := Measure.pi_map_pi (μ := fun _ : ι => lebR0 k r N.j β)
      (f := fun v => lmulM (Matrix.of (m s v))) fun v => (continuous_lmulM _).measurable.aemeasurable
    simp only [e] at this
    exact this
  have conv : ∀ (Γ : Subgroup (V ≃ₗ[K] V)) (Ω : Set (ι → Mt k r)), IsFund (realPts Φ (Γ : Set (V ≃ₗ[K] V))) (RP k r g) Ω →
      ∀ x ∈ RP k r g, ∃! s, s ∈ Γ ∧ mulP (m s) x ∈ Ω := by
    intro Γ Ω h x hx
    obtain ⟨m0, ⟨⟨s, hs, hsm⟩, hΩ⟩, hun⟩ := h.2 x hx
    have e : m0 = m s := hmu s m0 hsm
    refine ⟨s, ⟨hs, e ▸ hΩ⟩, fun t ht => ?_⟩
    have e2 : m t = m0 := hun _ ⟨⟨t, ht.1, hm t⟩, ht.2⟩
    exact hsep t s hι fun v x => by rw [← hm t v x, ← hm s v x, e2, e]
  obtain ⟨hLU, -, hz1, -, hRefLat, -⟩ := GlobalTheory.DegCnt.InnerLat.main K V H hK r N gg Λ hgg hT
  have hzL : N.F.z ∈ latL N.F N.F' Λ := by
    have := (hz1 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)
    simpa using this
  have hΛdata := ((GlobalTheory.HermLat.isUnimod_iff H Λ).1 hT.1.1).1
  have hΛ : Submodule.IsFullLattice K Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg K hΛdata.1, span_eq_top := hΛdata.2 }
  have hRefFull : Submodule.IsFullLattice K (N.Ref (latL N.F N.F' Λ)) := by
    refine { toIsLattice := hRefLat, span_eq_top := ?_ }
    obtain ⟨-, -, hC, -, hWn, hUp, -, -, -, -, -, hPi⟩ :=
      GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
    have hP : N.Pi ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      rw [hPi, ← GlobalTheory.DegCnt.InnerLat.span_hermFramePair_lattice_eq_sup N]
      exact Submodule.span_mono (show (N.P0 : Set V) ⊆ N.Ref (latL N.F N.F' Λ) from
        fun _ hx => Submodule.mem_sup_left hx)
    have hW : N.Wt ≤ Submodule.span K (N.Ref (latL N.F N.F' Λ) : Set V) := by
      intro x hx
      have hxW : x ∈ N.Wn := by rw [hWn]; exact Submodule.mem_sup_left hx
      obtain ⟨c, hc, hcx⟩ := GlobalTheory.DegCnt.InnerLat.exists_mult hΛdata.2 x
      rw [← Submodule.smul_mem_iff _ hc]
      apply Submodule.subset_span
      apply Submodule.mem_sup_right
      refine ⟨⟨?_, Submodule.mem_sup_left hcx⟩, N.Wn.smul_mem c hxW⟩
      rw [hUp]
      exact Submodule.mem_sup_left (N.Wn.smul_mem c hxW)
    apply eq_top_iff.mpr
    rw [← hC.sup_eq_top]
    exact sup_le hW hP
  obtain ⟨Ω, hΩ, -, hΩle⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds K V H hK r N k ι σ β Φ z z' g hP hd hF hN hv (latL N.F N.F' Λ) hLU hzL
  have hnil := (GlobalTheory.UnipStab.common_unipotent_stabiliser K V H hK r N).2.2.2.2
  have hc1 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hRefFull hΛ).1
  have hc2 := (GlobalTheory.DegCnt.Unimod.invVol_smul K V N.R (2 * r + 1) hnil _ _ hΛ hRefFull).1
  haveI := countable_aut K V
  have key := covol_of_act (fun s x => mulP (m s) x) h1 h2 (Measure.pi fun _ : ι => lebR0 k r N.j β) (RP k r g)
    (N.Gam (N.Ref (latL N.F N.F' Λ))) (N.Gam Λ) Ω Kf hmeas inferInstance inferInstance hnull
    (fun s hs => by
      have hsR : s ∈ N.R := (sup_le inf_le_left inf_le_left : _ ≤ N.R) hs
      exact ⟨fun x hx v => rset_mul (hu v) (hmR s hsR v) (hx v), hpres s hsR⟩)
    hc1 hc2 hΩ.1 hKf.1 (conv _ _ hΩ) (conv _ _ hKf)
  have hom : 0 ≤ N.om Λ := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [key, ENNReal.ofReal_mul hom]
  exact mul_le_mul_right hΩle _

end GlobalTheory.DegVol.Cov
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.integrable_bessel_fubini_integrand_prod : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v (Matrix.of p.2 * Matrix.of p.1)) * ⟪PiS (psiGen k r z c) π (Matrix.of p.2)⁻¹ ξ, ξ⟫_ℂ) (μG.prod μS) := by
  first | exact @GlobalTheory.SgInf.prod_integrand_integrable | exact GlobalTheory.SgInf.prod_integrand_integrable | (intros; apply GlobalTheory.SgInf.prod_integrand_integrable <;> assumption)
end

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapLine

theorem psi_const_gap : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := by
  intro k r z c g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

theorem line_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ} {σ : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hk : 1 ≤ k) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {B0 B : H → Wp}
    (h0 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B0)
    (h1 : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z c) σ π B)
    {x0 : H} (hx0 : x0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) (hne : B0 x0 ≠ 0) :
    ∃ κ : ℂ, ∀ x ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, B x = κ • B0 x := by
  have hpsi : Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := funext (psi_const_gap k r z c)
  rw [hpsi] at h0 h1
  obtain ⟨a, b, hab, hrel⟩ :=
    hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B0 h1 h0
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := hab.resolve_left (fun h => h rfl)
    have := hrel x0 hx0
    simp only [zero_smul, zero_add] at this
    exact hne ((smul_eq_zero.mp this).resolve_left hb)
  refine ⟨-(b / a), fun x hx => ?_⟩
  have h' : a • B x = -(b • B0 x) := eq_neg_of_add_eq_zero_left (hrel x hx)
  calc B x = a⁻¹ • (a • B x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = -(b / a) • B0 x := by rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem bessel_line_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l l₁ : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsBes R z π l → NzOn R l → IsBes R z π l₁ → ∃ c : ℂ, ∀ v ∈ R.sm, l₁ v = c • l v := by
  intro hH k r ε mu R Wp _ _ _ _ z π u μW μN μG νq l l₁ hDG hS hl hnz hl₁
  obtain ⟨w, hw, hne⟩ := hnz
  obtain ⟨hz, hT, ⟨u₀, hπ⟩, -⟩ := hS
  obtain ⟨h, hgap, hk, hh, -, -⟩ := hDG.gap
  have hc : Formalism.QuantumDeterminants.cStd ≠ 0 := by
    unfold Formalism.QuantumDeterminants.cStd
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact line_of_uniqGap hH.2.1 hk hgap hh hDG.hc hDG.ds hz hT hc hπ hl hl₁ hw hne

end GlobalTheory.GapLine
end

section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputsGap

open GlobalTheory.Amp.LocalInputs

theorem multOne_of_uniqGap (hU : GlobalTheory.GapIn.UniqGap) {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {π : Mat k r → (Wp →L[ℂ] Wp)} {h : ℝ}
    (hk : 1 ≤ k) (hg : GapAtLeast ε lam h) (hh : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h)
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z) (hc : c ≠ 0)
    (hπ : IsHCTypeW k r z u π) : MultOne z (psi k r z c) σ π := by
  intro B B' h1 h'
  rw [GlobalTheory.BesselMultOne.psi_eq_psiGen] at h1 h'
  obtain ⟨a, b, hab, e⟩ := hU k r ε lam h H σ z (fun _ => c) u Wp π hk hg hh hl hσ hz hT (fun _ => hc) hπ B B'
    (GlobalTheory.BesselMultOne.isBesselMapSm_of h1) (GlobalTheory.BesselMultOne.isBesselMapSm_of h')
  rcases hab with ha | hb
  · refine ⟨-(a⁻¹ * b), Or.inl fun v hv => ?_⟩
    have h3 : a • B v = -(b • B' v) := eq_neg_of_add_eq_zero_left (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · refine ⟨-(b⁻¹ * a), Or.inr fun v hv => ?_⟩
    have h3 : b • B' v = -(a • B v) := eq_neg_of_add_eq_zero_right (e v hv)
    rw [neg_smul, mul_smul, ← smul_neg, ← h3, smul_smul, inv_mul_cancel₀ hb, one_smul]

theorem gap_small_le {k r : ℕ} (hk : 1 ≤ k) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 19 := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn2 : 2 ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (0 : ℝ) ≤ r := by positivity
    rw [hn]; push_cast; linarith
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
  rw [this]; gcongr

theorem locIn_of_hypGap : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH Cg cb Cu cT CT C0
  have hU : GlobalTheory.GapIn.UniqGap := hH.2.1
  have hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow := hH.1.1.1
  refine ⟨0, fun D large₂ C' Cl hB hZ τ w w' θ W hTT hW A hA => ?_⟩
  obtain ⟨c1, c2, z1, z2, t1, t2, -⟩ := hW
  obtain ⟨hl, hds, -, -, -, -, ⟨P, hP, hv⟩, -⟩ := hA
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv1, -, hgap, -, -, -, hCl⟩, -, -⟩ := hZ
  have hT1 : 0 < Tz D.R.k D.R.rS W.z := by
    rw [t1]; unfold Tr; exact_mod_cast hTT.1.pos
  have hT2 : 0 < Tz D.R.k D.R.rS W.z' := by
    rw [t2]; unfold Tr; exact_mod_cast hTT.2.1.pos
  have hc : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
    have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
    have hka : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    exact Complex.ofReal_ne_zero.2 (by positivity)
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hmf : (D.R.m : ℝ) ≤ D.R.f := by exact_mod_cast D.R.m_le_f
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hf5 : (D.R.m : ℝ) ≤ (D.R.f : ℝ) ^ 5 := hmf.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hge : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    rw [dimS_eq]
    calc (D.R.r : ℝ) ^ 19 = 1 * (D.R.r : ℝ) ^ 19 * 1 := by ring
      _ ≤ (Cl * D.R.m) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr; exact hB.2.1
      _ ≤ (Cl * (D.R.f : ℝ) ^ 5) * (D.R.r : ℝ) ^ 19 * large₂.sc.L := by gcongr
      _ = _ := by ring
  have hg := gap_of_nodes D τ _ hl.1 fun j h1 h2 => hge.trans (hgap τ j h1 h2)
  have hh := gap_small_le (r := D.R.rS) hk
  refine ⟨multOne_of_uniqGap hU hk hg hh hl hds z1 hT1 hc c1,
    multOne_of_uniqGap hU hk hg hh hl hds z2 hT2 hc c2, ?_⟩
  refine (decay_span (by positivity) (urep_of_ds hds) (decay_low hD hk hl hds hg hP)).mono ?_
  exact Submodule.span_mono fun v ⟨g, hg, e⟩ => ⟨g, hg, _, hv, e⟩

end GlobalTheory.Amp.LocalInputsGap
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapAmpTK

open GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.GapAmpTK
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.AmpTKGap

theorem isCoef_kfin_and_torus_translate : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  intro H k r L l l' κ τ hκ hτ f hf
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (GlobalTheory.AmpTK.rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hmain := (GlobalTheory.isCoef_of_translate_smul_exists H.1.1.2.2.1 k r L.ε L.lam (GlobalTheory.AmpTK.rep L) L.Wp L.Wq l l' hDS).1
  have hd := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH (k := k) (r := r) hκ hτ
  have h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ BranchingSupport.GG k r := by
    have := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd hdi
    rwa [Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ] at this
  obtain ⟨P, Q, hQ, hP, h⟩ := hf
  refine ⟨hmain f ⟨1, h1, 1, h1, P, Q, hQ, hP, fun g => ?_⟩, hmain _ ⟨_, hd, _, hdi, P, Q, hQ, hP, fun g => ?_⟩⟩
  · exact (congrArg f (by simp : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * 1 = g)).trans (h g)
  · exact (congrArg f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj_cjI hκ hτ g)).trans (h g)

end GlobalTheory.AmpTKGap

end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.lintegral_gaussian_hermitianNormFibre_eq_deriv : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β d : ℝ), IsDxDq fib → β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Sp P Q | qf y ≤ t}, gaussSp y) d β → ∫⁻ y, ENNReal.ofReal (gaussSp y) ∂(fib β) = ENNReal.ofReal (2 ^ (P + Q) * d) := by
  first | exact @GlobalTheory.GaussFibre.gauss_fibre | exact GlobalTheory.GaussFibre.gauss_fibre | (intros; apply GlobalTheory.GaussFibre.gauss_fibre <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.complementary_block_unitary_forms : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → (τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) → n = n₀ + 2 * ∑ i, j i → (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → (∀ i k, (A i)ᴴ * Formalism.REAL.Jm ε * A k = 0) → (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → SpansFlag A W → IsIsoFlag ε j W → ∃ θ, IsLeviChart ε ε₀ W A A₀ τ τ₀ θ := by
  first | exact @GlobalTheory.LeviIso.Chart.exists_leviChart | exact GlobalTheory.LeviIso.Chart.exists_leviChart | (intros; apply GlobalTheory.LeviIso.Chart.exists_leviChart <;> assumption)
end
