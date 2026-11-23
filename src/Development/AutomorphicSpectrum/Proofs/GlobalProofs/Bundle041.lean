module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreserved
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsIrrKSubOfIsKTypeOf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import CompanionTheory.AutomorphicTheory.HarishChandraMultiplicity.HCMult
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.HarishChandraModulesIndefiniteUnitaryGroup
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SubquotientNontrivial
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SymmetricPowerMatrix
import Development.WeilBound.HeckeVectors.SmoothVectors.SobolevApproximation.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCPX
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import GroundTheory.GlobalFields.TateThesis.HeckeChar
public import ReciprocityTheory.Hypotheses.GalCoh
public import Formalism.GaloisCohomology.StatementLoc
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle339
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle002
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle001
public import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
import Development.AutomorphicSpectrum.PublishedTheorems.Jets₂.IsPermissibleOfCentre
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def IsIrrK (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  FiniteDimensional ℂ S ∧ IsKStable G π S ∧
    ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S

def isoGens (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Set (Submodule ℂ H) :=
  {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)}

theorem orthogonal_kstable (hG : IsLinRed G) (hA : IsAdmOn G π) {S : Submodule ℂ H}
    (hS : IsKStable G π S) : IsKStable G π Sᗮ := by
  intro k hk y hy
  rw [Submodule.mem_orthogonal]
  intro s hs
  have hk' : star k ∈ maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
  have h1 : π k (π (star k) s) = s := by
    have hm : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    rw [← ContinuousLinearMap.comp_apply, ← hA.1.2 k hk.1 (star k) hk'.1, hm, hA.1.1]
    rfl
  let Lk : H →ₗᵢ[ℂ] H := ⟨(π k : H →ₗ[ℂ] H), hA.2.2.1 k hk⟩
  have h2 : inner ℂ (π k (π (star k) s)) (π k y) = inner ℂ (π (star k) s) y := Lk.inner_map_map _ _
  rw [← h1, h2]
  exact Submodule.inner_right_of_mem_orthogonal (hS _ hk' s hs) hy

theorem sSup_kstable {A : Set (Submodule ℂ H)} (hA : ∀ S ∈ A, IsKStable G π S) :
    IsKStable G π (sSup A) := by
  intro k hk w hw
  have h : sSup A ≤ (sSup A).comap (π k : H →ₗ[ℂ] H) :=
    sSup_le fun S hS x hx => Submodule.mem_comap.2 (le_sSup hS (hA S hS k hk x hx))
  exact h hw

theorem exists_irr_family (hG : IsLinRed G) (hA : IsAdmOn G π) (m : ℕ) :
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → Module.finrank ℂ S = m → IsKStable G π S →
      ∃ F : Set (Submodule ℂ H), F.Finite ∧ (∀ I ∈ F, IsIrrK G π I) ∧ S ≤ sSup F := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hfin hm hS
    by_cases hirr : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S
    · refine ⟨{S}, Set.finite_singleton S, ?_, ?_⟩
      · rintro I rfl
        exact ⟨hfin, hS, hirr⟩
      · simp
    · push_neg at hirr
      obtain ⟨S', hle, hS', hne0, hneS⟩ := hirr
      haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hle
      have hlt : S' < S := lt_of_le_of_ne hle hneS
      have hT : IsKStable G π (S ⊓ S'ᗮ) := fun k hk v hv =>
        ⟨hS k hk v hv.1, orthogonal_kstable hG hA hS' k hk v hv.2⟩
      haveI : FiniteDimensional ℂ (S ⊓ S'ᗮ : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_left
      have hltT : S ⊓ S'ᗮ < S := by
        refine lt_of_le_of_ne inf_le_left fun h => hne0 ?_
        have hSo : S ≤ S'ᗮ := inf_eq_left.1 h
        rw [eq_bot_iff]
        intro x hx
        have h0 : ⟪x, x⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal hx (hSo (hle hx))
        exact (Submodule.mem_bot ℂ).2 (inner_self_eq_zero.1 h0)
      have hd₁ : Module.finrank ℂ S' < m := hm ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have hd₂ : Module.finrank ℂ (S ⊓ S'ᗮ : Submodule ℂ H) < m :=
        hm ▸ Submodule.finrank_lt_finrank_of_lt hltT
      obtain ⟨F₁, hF₁, hI₁, hle₁⟩ := ih _ hd₁ S' inferInstance rfl hS'
      obtain ⟨F₂, hF₂, hI₂, hle₂⟩ := ih _ hd₂ (S ⊓ S'ᗮ) inferInstance rfl hT
      refine ⟨F₁ ∪ F₂, hF₁.union hF₂, ?_, ?_⟩
      · rintro I (hI | hI)
        · exact hI₁ I hI
        · exact hI₂ I hI
      · intro v hv
        have hp : ((S'.orthogonalProjection v : S') : H) ∈ S' := (S'.orthogonalProjection v).2
        have hq : v - (S'.orthogonalProjection v : H) ∈ S ⊓ S'ᗮ :=
          ⟨S.sub_mem hv (hle hp), Submodule.sub_starProjection_mem_orthogonal (K := S') v⟩
        have e : v = (S'.orthogonalProjection v : H) + (v - (S'.orthogonalProjection v : H)) := by abel
        rw [e, sSup_union]
        exact Submodule.add_mem _ (Submodule.mem_sup_left (hle₁ hp)) (Submodule.mem_sup_right (hle₂ hq))

theorem isoGens_kstable {S S' : Submodule ℂ H} (hS : IsKStable G π S) (h : S' ∈ isoGens G π S) :
    IsKStable G π S' := by
  obtain ⟨T, rfl, hT⟩ := h
  rintro k hk _ ⟨s, hs, rfl⟩
  exact ⟨π k s, hS k hk s hs, hT k hk s hs⟩

theorem le_sSup_isoGens (S : Submodule ℂ H) : S ≤ sSup (isoGens G π S) := by
  refine le_trans (le_of_eq ?_) (le_sSup (show S.map LinearMap.id ∈ isoGens G π S from
    ⟨LinearMap.id, rfl, fun k _ w _ => rfl⟩))
  simp

theorem map_mem_of_gen {Y S S' : Submodule ℂ H} (hSY : sSup (isoGens G π S) ≤ Y) (h : S' ∈ isoGens G π S)
    (D : Y →ₗ[ℂ] H) (hD : ∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y))
    (hS : IsKStable G π S) {x : H} (hx : x ∈ S') (hxY : x ∈ Y) : D ⟨x, hxY⟩ ∈ Y := by
  obtain ⟨T, rfl, hT⟩ := h
  obtain ⟨s, hs, rfl⟩ := hx
  have hTY : ∀ w ∈ S, T w ∈ Y := fun w hw =>
    hSY (le_sSup (show S.map T ∈ isoGens G π S from ⟨T, rfl, hT⟩) ⟨w, hw, rfl⟩)
  let f : S →ₗ[ℂ] H := D ∘ₗ (T.domRestrict S).codRestrict Y (fun w => hTY w w.2)
  obtain ⟨T', hT'⟩ := LinearMap.exists_extend f
  have hval : ∀ w (hw : w ∈ S), T' w = D ⟨T w, hTY w hw⟩ := fun w hw =>
    LinearMap.congr_fun hT' ⟨w, hw⟩
  have hcomm : ∀ k ∈ maxCpt G, ∀ w ∈ S, T' (π k w) = π k (T' w) := by
    intro k hk w hw
    rw [hval _ (hS k hk w hw), hval w hw]
    exact hD k hk _ _ (hT k hk w hw)
  have hmem : S.map T' ∈ isoGens G π S := ⟨T', rfl, hcomm⟩
  have : T' s ∈ Y := hSY (le_sSup hmem ⟨s, hs, rfl⟩)
  rwa [hval s hs] at this

theorem exists_isotypic_sum : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hA : IsAdmOn G π) {v : H} (hv : IsKFinOn G π v), ∃ Y : Submodule ℂ H, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ IsKStable G π Y ∧ ∀ D : Y →ₗ[ℂ] H, (∀ k ∈ maxCpt G, ∀ y y' : Y, (y' : H) = π k y → D y' = π k (D y)) → ∀ y, D y ∈ Y := by
  intro n G H _ _ _ π hG hA v hv
  obtain ⟨S, hfin, hvS, hS⟩ := hv
  obtain ⟨F, hF, hI, hle⟩ := exists_irr_family hG hA _ S hfin rfl hS
  let iso : Submodule ℂ H → Submodule ℂ H := fun I => sSup (isoGens G π I)
  have hisoK : ∀ I ∈ F, IsKStable G π (iso I) := fun I hIF =>
    sSup_kstable fun S' h => isoGens_kstable (hI I hIF).2.1 h
  have hisoF : ∀ I ∈ F, FiniteDimensional ℂ (iso I) := fun I hIF =>
    hA.2.2.2 I (hI I hIF).1 (hI I hIF).2.1 (hI I hIF).2.2
  have hYle : ∀ I ∈ F, iso I ≤ sSup (iso '' F) := fun I hIF => le_sSup ⟨I, hIF, rfl⟩
  refine ⟨sSup (iso '' F), ?_, ?_, ?_, ?_⟩
  · rw [sSup_eq_iSup']
    haveI : Finite ↥(iso '' F) := (hF.image iso).to_subtype
    haveI : ∀ a : ↥(iso '' F), FiniteDimensional ℂ (a : Submodule ℂ H) := by
      rintro ⟨_, I, hIF, rfl⟩
      exact hisoF I hIF
    exact Submodule.finiteDimensional_iSup _
  · exact (sSup_le fun I hIF => (le_sSup_isoGens I).trans (hYle I hIF)) (hle hvS)
  · refine sSup_kstable ?_
    rintro _ ⟨I, hIF, rfl⟩
    exact hisoK I hIF
  · intro D hD y
    have hP : sSup (iso '' F) ≤ ((sSup (iso '' F)).comap D).map (sSup (iso '' F)).subtype := by
      refine sSup_le ?_
      rintro _ ⟨I, hIF, rfl⟩
      refine sSup_le fun S' hS' x hx => ?_
      have hxY : x ∈ sSup (iso '' F) := hYle I hIF (le_sSup hS' hx)
      exact ⟨⟨x, hxY⟩, map_mem_of_gen (hYle I hIF) hS' D hD (hI I hIF).2.1 hx hxY, rfl⟩
    obtain ⟨y', hy', he⟩ := hP y.2
    have hyy : y' = y := Subtype.ext he
    subst hyy
    exact hy'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Isotypic

end
end

section


theorem _root_.GlobalTheory.T.gl_relations_triangular_annihilation : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | exact GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | (intros; apply GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block <;> assumption)
end

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.KFinLink

open GlobalTheory.KFinVec
open ReciprocityTheory.ChartRestriction.DS (smD smE smE_apply isDerivedOn_smE dS dS_eq_actM actM)
open CompanionTheory.D.gk.HC (KF)

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dRep_eq_dS (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    Formalism.L2.Theta.dRep σ X w = dS σ X w := by
  unfold Formalism.L2.Theta.dRep dS
  congr 1

theorem isAdmissible_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsAdmissible ε σ := by
  rintro S ⟨hf, -, hK, -⟩
  have hfin : FiniteDimensional ℂ (Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S) :=
    (CompanionTheory.HCMult.harish_chandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMult) n ε H σ hσ hirr S hf hK
  have hle : kIsotypic ε σ S ≤ Formalism.MainNotions.BridgeCPX.eqImg (fun k : Formalism.REAL.KG ε => σ (Formalism.REAL.toMK k)) S :=
    iSup_le fun T => le_sSup ⟨T.1, fun a v w h => T.2 _ a.2 v w h, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem isLieStable_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : IsLieStable ε σ (kFinSub ε σ) := by
  intro X hX v hv
  obtain ⟨h1, h2⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  have hvS : v ∈ smD ε σ := h1 v hv
  rw [dRep_eq_dS]
  have e := dS_eq_actM (isDerivedOn_smE hσ) hX ⟨v, hvS⟩
  simp only [] at e
  rw [e]
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (h2 a b ⟨v, hvS⟩ hv)

theorem lieIrr_of [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (S : Submodule ℂ H) (hS : S ≤ kFinSub ε σ)
    (hL : IsLieStable ε σ S) : S = ⊥ ∨ S = kFinSub ε σ := by
  obtain ⟨h1, -⟩ := CompanionTheory.D.gk.HC.K_finite_smooth_vectors n ε H σ hσ hirr
  let N : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hNK : (N : Set (smD ε σ)) ⊆ KF ε σ := fun v hv => hS hv
  have hst : ∀ a b, ∀ v ∈ N, smE ε σ a b v ∈ N := by
    intro a b v hv
    show ((smE ε σ a b v : smD ε σ) : H) ∈ S
    rw [smE_apply hσ]
    have e1 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart1 ε (Matrix.single a b 1)) (v : H) hv
    have e2 := hL _ (ReciprocityTheory.ChartRestriction.DS.SmDerA.inG_cpart2 ε (Matrix.single a b 1)) (v : H) hv
    rw [dRep_eq_dS] at e1 e2
    exact S.add_mem e1 (S.smul_mem _ e2)
  rcases CompanionTheory.D.gk.HC.uIrr n ε H σ hσ hirr N hNK hst with h | h
  · left
    refine eq_bot_iff.2 fun v hv => ?_
    have hvN : (⟨v, h1 v (hS hv)⟩ : smD ε σ) ∈ N := hv
    rw [h] at hvN
    have := (Submodule.mem_bot ℂ).1 hvN
    exact (Submodule.mem_bot ℂ).2 (congrArg Subtype.val this)
  · right
    refine le_antisymm hS fun v hv => ?_
    have hvK : (⟨v, h1 v hv⟩ : smD ε σ) ∈ KF ε σ := hv
    rw [← h] at hvK
    exact hvK

end GlobalTheory.CompanionTheory.KFinLink

namespace GlobalTheory.CompanionTheory.Published

theorem kFiniteVectors_irreducibleUnitary_unitaryGroupPQ : GlobalTheory.Published.KFiniteVectorsUnitary := by
  intro n ε H _ _ _ _ σ hσ hirr
  exact ⟨GlobalTheory.CompanionTheory.KFinLink.isAdmissible_of hσ hirr,
    CompanionTheory.D.gk.HC.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hσ hirr,
    CompanionTheory.D.gk.HC.kfinDense_UJC hσ,
    GlobalTheory.CompanionTheory.KFinLink.isLieStable_of hσ hirr,
    fun S hS hL => GlobalTheory.CompanionTheory.KFinLink.lieIrr_of hσ hirr S hS hL⟩

end GlobalTheory.CompanionTheory.Published

end
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps

namespace GlobalTheory.CompanionTheory.HeckeBridge

variable {E : Type} [Field E] [NumberField E]

def ideleCircle (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.IdeleGroup E →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul]
    rfl

theorem continuous_ideleCircle (χ : HChar E) (hu : IsUnitary χ) : Continuous (ideleCircle χ hu) :=
  Continuous.subtype_mk (Units.continuous_val.comp χ.2.1) _

def toHecke (χ : HChar E) (hu : IsUnitary χ) : GroundTheory.Global.HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift (GroundTheory.Global.IdeleGroup.diagonal E).range (ideleCircle χ hu) (by
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    have := χ.2.2 k
    show ((χ.1 (Neutral.B1.diagUnits E k) : ℂˣ) : ℂ) = 1
    rw [this]; rfl)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (GroundTheory.Global.IdeleGroup.diagonal E).range).continuous_iff.2
    (continuous_ideleCircle χ hu)

theorem coe_toIdele (χ : HChar E) (hu : IsUnitary χ) (x : GroundTheory.Global.IdeleGroup E) :
    (((toHecke χ hu).toIdele x : Circle) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) := rfl

theorem coe_localComponent (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    (((toHecke χ hu).localComponent v x : Circle) : ℂ) = ((χ.loc v x : ℂˣ) : ℂ) := rfl

theorem toHecke_inv (χ : HChar E) (hu : IsUnitary χ) (hu' : IsUnitary χ⁻¹) : toHecke χ⁻¹ hu' = (toHecke χ hu)⁻¹ := by
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  show (((toHecke χ⁻¹ hu').toIdele x : Circle) : ℂ) = ((((toHecke χ hu).toIdele x)⁻¹ : Circle) : ℂ)
  rw [coe_toIdele, Circle.coe_inv, coe_toIdele]
  exact Units.val_inv_eq_inv_val (χ.1 x)

end GlobalTheory.CompanionTheory.HeckeBridge
end
end

section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem exists_prime_mem_asIdeal {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal :=
  _root_.Bl.FirstLemmaD.goal1 v

theorem finCd2_GK (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R (GK p K) M) (hrho : ContAction rho) :
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧
      ∀ n, 3 ≤ n → Subsingleton (Hn rho n) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have : CharZero K := algebraRat.charZero K
  obtain ⟨A, _, e, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep (GK p K) R M rho hrho
  have : Finite A := Finite.of_equiv _ e.toEquiv
  have hn : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 (GK p K) R M rho A e he
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (GK p K) R M rho A e he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (GK p K) R M rho A e he
  have := finite_cohomology_localField A hn 0
  have := finite_cohomology_localField A hn 1
  have := finite_cohomology_localField A hn 2
  refine ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv,
    Finite.of_equiv _ e2.symm.toEquiv, fun n h => ?_⟩
  obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn (GK p K) R M rho A e he n
  have := subsingleton_cohomology_localField A hn n h
  exact en.toEquiv.subsingleton

theorem localFiniteness : ReciprocityTheory.Gal.LocalFiniteness := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', -⟩ := GlobalTheory.DecLocal.exists_mulEquiv_cyc F Ω p v A hpv hA
  let E : GK p K ≃ₜ* Dec (F := F) A :=
    { e.symm with continuous_toFun := he', continuous_invFun := he }
  have h : ReciprocityTheory.Neutral.Bridge.FinCd2 (rho.comp (E : GK p K →* Dec (F := F) A)) :=
    finCd2_GK p K hK _ M _ (ReciprocityTheory.Neutral.Bridge.contAction_comp E hc)
  exact ReciprocityTheory.Neutral.Bridge.FinCd2.of_comp E h

end GlobalTheory.CompanionTheory.Hypotheses₂
end
