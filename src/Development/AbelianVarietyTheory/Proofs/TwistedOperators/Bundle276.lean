module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle269
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle264
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle246
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle261
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle140

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_rat_moves | exact GlobalTheory.Ker.LevMove.levK_of_rat_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_rat_moves <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_multiplier_standard_lattice_of_mover_trivial : ∀ (D : D7) (S : HSp D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank) (σ : Af D.host.F) (w : HeightOneSpectrum (𝓞 D.host.F)), evalV D.host.F w σ = 0 → (∀ i j, (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ)) * (mt S k₀⁻¹ - 1) i j = 0) → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ v ∈ Λ', ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • v ∈ stdL D.host.E S.rank := by
  first | exact @GlobalTheory.Ker.MoverStd.exists_mul_std | exact GlobalTheory.Ker.MoverStd.exists_mul_std | (intros; apply GlobalTheory.Ker.MoverStd.exists_mul_std <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_completedMatrixGroup_of_local_multiplier : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  first | exact @GlobalTheory.HatPoint.mem_hatA_of_div | exact GlobalTheory.HatPoint.mem_hatA_of_div | (intros; apply GlobalTheory.HatPoint.mem_hatA_of_div <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevkLoc

theorem smul_mem_of_isAA {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (h : IsAA Λ ΛT) (c : D.host.E)
    (hc : ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c * x) : ∀ x ∈ Λ, c • x ∈ ΛT := by
  intro x hx
  have hx' := (h x).1 hx
  clear hx
  induction hx' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, t, ht, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hc a ha
    rw [smul_smul, ← hb]
    have : ((b : D.host.E)) • t = b • t := (algebraMap_smul D.host.E b t)
    rw [this]
    exact ΛT.smul_mem b ht
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact ΛT.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact ΛT.neg_mem hx

theorem smul_mem_ideal_smul {D : D7} {k : ℕ} {Λ ΛT : Lt D.host.E k} (P : Ideal (𝓞 D.host.E)) (c : D.host.E)
    (h : ∀ x ∈ Λ, c • x ∈ ΛT) : ∀ x ∈ P • Λ, c • x ∈ P • ΛT := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun p hp y hy => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul hp (h y hy)
  · rw [smul_add]; exact Submodule.add_mem _ hx hy

theorem congr_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (P : Ideal (𝓞 D.host.E)), P.IsPrime → IsAA Λ ΛT →
    ∀ m : Matrix (Fin k) (Fin k) (AfE D), (∀ u ∈ hatV Λ, m *ᵥ u - u ∈ hatV (P • Λ)) →
    ∃ b : 𝓞 D.host.E, b ∉ P ∧ ∀ u ∈ hatV ΛT,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • (m *ᵥ u - u) ∈ hatV (P • ΛT) := by
  intro D k Λ ΛT P hP hAA m hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity D
  choose b hb using fun i => hc i (a i) (ha i)
  have hb1 : ∑ i, b i = 1 := by
    have : ((∑ i, b i : 𝓞 D.host.E) : D.host.E) = ((1 : 𝓞 D.host.E) : D.host.E) := by
      push_cast
      rw [← hsum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]; exact hb i
    exact RingOfIntegers.ext this
  obtain ⟨i, hi⟩ : ∃ i, b i ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hb1]
    exact Ideal.sum_mem _ fun i _ => hcon i
  refine ⟨b i, hi, fun u hu => ?_⟩
  have hA : ∀ t ∈ ΛT, a i • t ∈ Λ := fun t ht =>
    (hAA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, t, ht, rfl⟩)
  have hC : ∀ x ∈ P • Λ, c i • x ∈ P • ΛT :=
    smul_mem_ideal_smul P (c i) (smul_mem_of_isAA hAA (c i) (hc i))
  have hu' := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D ΛT Λ (a i) hA u hu
  have h1 := hm _ hu'
  have h2 := GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D (P • Λ) (P • ΛT) (c i) hC _ h1
  convert h2 using 1
  rw [Matrix.mulVec_smul, ← smul_sub, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hb i]

end GlobalTheory.LevkLoc
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevMoveAA

theorem isMov_of_isAA : ∀ (D : D7) {k : ℕ} (Λ ΛT : Lt D.host.E k) (m : Matrix (Fin k) (Fin k) (AfE D)),
    IsAA Λ ΛT → IsMov m Λ Λ → IsMov m ΛT ΛT := by
  intro D k Λ ΛT m hA hm
  obtain ⟨n, a, c, ha, hc, hsum⟩ := GlobalTheory.T.cmHostFractionalIdeal_partitionOfUnity D
  have h1 : ∀ i, ∀ x ∈ ΛT, a i • x ∈ Λ := fun i x hx =>
    (hA _).2 (AddSubgroup.subset_closure ⟨a i, ha i, x, hx, rfl⟩)
  have h2 : ∀ i, ∀ x ∈ Λ, c i • x ∈ ΛT := by
    intro i x hx
    have hx' := (hA x).1 hx
    clear hx
    induction hx' using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨a', ha', t, ht, rfl⟩ := hu
      obtain ⟨b, hb⟩ := hc i a' ha'
      rw [smul_smul, ← hb]
      exact ΛT.smul_of_tower_mem b ht
    | zero => simp
    | add x y _ _ ihx ihy => rw [smul_add]; exact ΛT.add_mem ihx ihy
    | neg x _ ihx => rw [smul_neg]; exact ΛT.neg_mem ihx
  have hs1 : ∀ i, ∀ u ∈ hatV ΛT, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u ∈ hatV Λ :=
    fun i => GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D ΛT Λ (a i) (h1 i)
  have hs2 : ∀ i, ∀ u ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • u ∈ hatV ΛT :=
    fun i => GlobalTheory.T.smul_mem_hermitianLatticeAdelicCompletion_of_smul_le D Λ ΛT (c i) (h2 i)
  have key : ∀ u : Fin k → AfE D,
      ∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = u := by
    intro u
    simp_rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Finset.sum_smul,
      ← TensorProduct.tmul_sum]
    rw [show ∑ i, c i * a i = 1 by rw [← hsum]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _]
    rw [← Algebra.TensorProduct.one_def, one_smul]
  intro u
  constructor
  · intro hu
    have hw : ∀ i, ∃ w ∈ hatV Λ, ((1 : Af D.host.F) ⊗ₜ[D.host.F] a i) • u = m *ᵥ w :=
      fun i => (hm _).1 (hs1 i u hu)
    choose w hwΛ hwe using hw
    refine ⟨∑ i, ((1 : Af D.host.F) ⊗ₜ[D.host.F] c i) • w i,
      AddSubgroup.sum_mem _ fun i _ => hs2 i _ (hwΛ i), ?_⟩
    rw [Matrix.mulVec_sum]
    conv_lhs => rw [← key u]
    exact Finset.sum_congr rfl fun i _ => by rw [hwe i, Matrix.mulVec_smul]
  · rintro ⟨u₀, hu₀, rfl⟩
    rw [← key u₀, Matrix.mulVec_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    exact hs2 i _ ((hm _).2 ⟨_, hs1 i u₀ hu₀, rfl⟩)

end GlobalTheory.LevMoveAA

end
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCUnitary

variable {n : ℕ} {ε : Fin n → Bool}

theorem maxCpt_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.maxCpt (UJset ε) = Kset ε := by
  ext g
  refine ⟨fun hg => ⟨hg.2, ?_⟩, fun hg => ⟨mem_UJset_of_mem_Kset hg, hg.1⟩⟩
  have h1 : g * gᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hg.2
  have h2 : gᴴ * Jm ε * g = Jm ε := hg.1
  calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [h2]
    _ = Jm ε * g := by rw [Matrix.mul_assoc, ← Matrix.mul_assoc g, h1, Matrix.one_mul]

theorem isLinRed_UJset (ε : Fin n → Bool) : GlobalTheory.LinRed.IsLinRed (UJset ε) := by
  have hW : IsIsoFlag ε (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (⊥ : Submodule ℂ (Fin n → ℂ))) :=
    ⟨rfl, monotone_const, fun i => i.elim0, fun x hx y _ => by
      rw [(Submodule.mem_bot ℂ).1 hx]; simp⟩
  have h := (GlobalTheory.T.leviModulusOne_linearReductive_exp_mul_exp n ε 0 _ _ hW (fun i => i.elim0)).1
  rwa [leviOne_zero hW, mats_top] at h

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isKStable_iff {S : Submodule ℂ H} : GlobalTheory.LinRed.IsKStable (UJset ε) π S ↔ IsKStableOn ε π S := by
  unfold GlobalTheory.LinRed.IsKStable IsKStableOn
  rw [maxCpt_UJset]

theorem isKTypeOf_map {Λ : Fin n → ℝ} {S : Submodule ℂ H} (hS : IsKTypeOf ε π Λ S) (T : H →ₗ[ℂ] H)
    (hT : ∀ k ∈ Kset ε, ∀ w ∈ S, T (π k w) = π k (T w)) : S.map T = ⊥ ∨ IsKTypeOf ε π Λ (S.map T) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hv⟩, hdom⟩ := hS
  have hpre : ∀ S' : Submodule ℂ H, IsKStableOn ε π S' → IsKStableOn ε π (S ⊓ S'.comap T) :=
    fun S' h k hk w hw => ⟨hst k hk w hw.1, by
      have : T (π k w) ∈ S' := by rw [hT k hk w hw.1]; exact h k hk _ hw.2
      exact this⟩
  have hbot : IsKStableOn ε π ⊥ := fun k _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _
  rcases hirr _ inf_le_left (hpre ⊥ hbot) with h0 | h1
  · right
    have hinj : ∀ w ∈ S, T w = 0 → w = 0 := fun w hw h => by
      have : w ∈ S ⊓ (⊥ : Submodule ℂ H).comap T := ⟨hw, h⟩
      rwa [h0, Submodule.mem_bot] at this
    refine ⟨inferInstance, ?_, fun S' hle hS' => ?_, ⟨T v, ⟨v, hvS, rfl⟩, fun h => hv0 (hinj v hvS h),
      fun θ hθ => ?_⟩, ?_⟩
    · rintro k hk _ ⟨w, hw, rfl⟩
      exact ⟨π k w, hst k hk w hw, hT k hk w hw⟩
    · rcases hirr _ inf_le_left (hpre S' hS') with h | h
      · left
        refine eq_bot_iff.2 fun x hx => ?_
        obtain ⟨w, hw, rfl⟩ := hle hx
        have : w ∈ S ⊓ S'.comap T := ⟨hw, hx⟩
        rw [h, Submodule.mem_bot] at this
        rw [this, map_zero]; exact Submodule.zero_mem _
      · exact Or.inr (le_antisymm hle (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h)))
    · rw [← hT _ hθ v hvS, hv θ hθ, map_smul]
    · rintro μ _ ⟨w, hw, rfl⟩ hw0 hwt
      refine hdom μ w hw (fun h => hw0 (by rw [h, map_zero])) fun θ hθ => ?_
      refine sub_eq_zero.1 (hinj _ (S.sub_mem (hst _ hθ w hw) (S.smul_mem _ hw)) ?_)
      rw [map_sub, map_smul, hT _ hθ w hw, hwt θ hθ, sub_self]
  · exact Or.inl (eq_bot_iff.2 (Submodule.map_le_iff_le_comap.2 (inf_eq_left.1 h1)))

theorem isAdmOn_iff [CompleteSpace H] : GlobalTheory.LinRed.IsAdmOn (UJset ε) π ↔ IsAdmRep ε π := by
  unfold GlobalTheory.LinRed.IsAdmOn IsAdmRep
  simp only [isKStable_iff]
  rw [maxCpt_UJset]
  refine and_congr_right fun h1 => and_congr_right fun h2 => and_congr_right fun h3 => ?_
  obtain ⟨hA, hB⟩ := GlobalTheory.KTypeHighest.ktype_highest_weight n ε H π h1 h2 h3
  refine ⟨fun h Λ => ?_, fun h S hfin hst hirr => ?_⟩
  · by_cases he : ∃ S₀, IsKTypeOf ε π Λ S₀
    · obtain ⟨S₀, hS₀⟩ := he
      haveI := h S₀ hS₀.1 hS₀.2.1 hS₀.2.2.1
      refine Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S' | ∃ T : H →ₗ[ℂ] H, S' = S₀.map T ∧
        ∀ k ∈ Kset ε, ∀ w ∈ S₀, T (π k w) = π k (T w)}) fun S hS => ?_)
      obtain ⟨B, hB1, hB2⟩ := hB Λ S₀ S hS₀ hS.2
      exact ⟨B, hB2.symm, fun k hk w _ => hB1 k hk w⟩
    · exact Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le fun S hS => absurd ⟨S, hS.2⟩ he)
  · by_cases h0 : S = ⊥
    · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) (sSup_le ?_)
      rintro _ ⟨T, rfl, -⟩
      rw [h0, Submodule.map_bot]
    · obtain ⟨Λ, hΛ⟩ := hA S hfin h0 hst hirr
      haveI := h Λ
      refine Submodule.finiteDimensional_of_le (S₂ := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε π Λ S}) (sSup_le ?_)
      rintro _ ⟨T, rfl, hT⟩
      rcases isKTypeOf_map hΛ T hT with hb | hk
      · rw [hb]; exact bot_le
      · exact le_sSup ⟨le_top, hk⟩

end GlobalTheory.HCUnitary
end

section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll.RatEll

theorem sig_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨-, -, -, h⟩ := h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h, h, star_star]

theorem exists_cls_of_irreducible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Function.Bijective (diagH σ J F) ∧ ∀ γ : GRat σ J, Irreducible γ.1.1.charpoly → ∃ P : PPol σ n, γ.1.1.charpoly = P.1 ∧ ∃ q, HasCls P F J (diagH σ J F γ) q := by
  intro F E _ _ _ _ _ σ hσ n J hJ
  refine ⟨GlobalTheory.T.unitaryRationalDiagonalHom_bijective F E σ n J, ?_⟩
  intro γ hirr
  have hm : Formalism.UG.cT (σ : E →+* E) γ.1.1 * J * γ.1.1 = J := γ.2
  have hs := GlobalTheory.T.charpoly_unitary_eq_conjugateReciprocal F E σ n J hJ.2 γ
  have hdet : γ.1.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp γ.1.isUnit).ne_zero
  have h0 : eval 0 γ.1.1.charpoly ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero]
    intro hc
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, hc, mul_zero]
  have hP : γ.1.1.charpoly.Monic ∧ Irreducible γ.1.1.charpoly ∧ γ.1.1.charpoly.natDegree = n ∧
      eval 0 γ.1.1.charpoly ≠ 0 ∧ γ.1.1.charpoly = sharp σ n γ.1.1.charpoly :=
    ⟨Matrix.charpoly_monic _, hirr, by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin], h0, hs⟩
  let P : PPol σ n := ⟨γ.1.1.charpoly, hP⟩
  refine ⟨P, rfl, ?_⟩
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_adjoinRoot_linearEquiv_of_charpoly_eq F E σ n P γ.1.1 rfl
  obtain ⟨x, hx0, hxs, hxf⟩ := GlobalTheory.T.exists_unitaryTorus_traceForm_of_hermitian F E σ (sig_sig hσ) n P J hJ γ.1.1 hm φ hφ
  exact GlobalTheory.T.exists_normClass_of_rationalIsometry_traceForm F E σ n P J φ x hx0 hxs hxf γ hφ

end GlobalTheory.TrEll.RatEll
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  first | exact @GlobalTheory.DblVac.gen_diag_anti_split_herm | exact GlobalTheory.DblVac.gen_diag_anti_split_herm | (intros; apply GlobalTheory.DblVac.gen_diag_anti_split_herm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DenInt

open IsDedekindDomain

theorem intRing_of_isIntegral {F : Type} [Field F] [NumberField F] {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Af F) c ∈ GlobalTheory.HolDict.ShortVec.intRing F := by
  refine GlobalTheory.HolDict.ShortVec.mem_intRing.2 fun v => ?_
  rw [AlgHom.commutes]
  refine Valued.toNormedField.norm_le_one_iff.2 ?_
  have := HeightOneSpectrum.valuation_le_one (K := F) v (⟨c, hc⟩ : 𝓞 F)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c).trans_le this

theorem exists_den (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  set b := Module.finBasis D.host.F D.host.E
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E
  obtain ⟨b', hb⟩ : ∃ b' : Fin (Module.finrank D.host.F D.host.E) → D.host.E,
      ∀ x k, Algebra.trace D.host.F D.host.E (b' k * x) = b.repr x k :=
    ⟨fun k => ((Algebra.traceForm D.host.F D.host.E).toDual (traceForm_nondegenerate D.host.F D.host.E)).symm (b.coord k),
      fun x k => LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate D.host.F D.host.E) (b.coord k) x⟩
  obtain ⟨d, hd, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (integralClosure ℤ D.host.E).toSubring b' fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b' k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨d, hd, fun x hx k => ?_⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k = algebraMap D.host.F (Af D.host.F) (b.repr x k) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.algebraMap_eq_smul_one]
  have e2 : (d : D.host.F) * b.repr x k = Algebra.trace D.host.F D.host.E (((d : D.host.E) * b' k) * x) := by
    rw [← hb, mul_assoc, ← nsmul_eq_mul d (b' k * x), map_nsmul, nsmul_eq_mul]
  have hi : IsIntegral ℤ ((d : D.host.F) * b.repr x k) := by
    rw [e2]
    exact Algebra.isIntegral_trace ((h k).mul hx)
  rw [e1, ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul]
  exact intRing_of_isIntegral hi

end GlobalTheory.DenInt
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordDenom

theorem finCoord_mul_denom : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  intro D
  set B := Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E) with hB
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (GlobalTheory.HolDict.ShortVec.intRing D.host.F)
    (fun p : Fin (Module.finrank D.host.F D.host.E) × Fin (Module.finrank D.host.F D.host.E) ×
      Fin (Module.finrank D.host.F D.host.E) => B.repr (B p.1 * B p.2.1) p.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  refine ⟨c, hc, fun e₁ e₂ a b ha hb k => ?_⟩
  have ha' : ∀ i, (e₁ : Af D.host.F) * B.repr a i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := ha
  have hb' : ∀ i, (e₂ : Af D.host.F) * B.repr b i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := hb
  change ((c * e₁ * e₂ : ℕ) : Af D.host.F) * B.repr (a * b) k ∈ _

  rw [← B.sum_repr a, ← B.sum_repr b, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_

  rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e : ((c * e₁ * e₂ : ℕ) : Af D.host.F) * (B.repr a i * B.repr b j * B.repr (B i * B j) k) =
      ((e₁ : Af D.host.F) * B.repr a i) * ((e₂ : Af D.host.F) * B.repr b j) * ((c : Af D.host.F) * B.repr (B i * B j) k) := by
    push_cast; ring
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (ha' i) (hb' j)) (h (i, j, k))

end GlobalTheory.CoordDenom
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.finite_levelDatumClasses : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  first | exact @GlobalTheory.LiftLevel.lvCls_finite | exact GlobalTheory.LiftLevel.lvCls_finite | (intros; apply GlobalTheory.LiftLevel.lvCls_finite <;> assumption)
end
