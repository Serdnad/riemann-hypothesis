module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle425
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle426
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle379
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle381
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle099
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle427
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle424
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.TripleAssembly

theorem darbAlg_le_schA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w),
    M.IsGood ψ → GlobalTheory.TripleAssembly.darbAlg M ψ τ ≤ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ n d Y Z M ψ τ hM
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, φ, -, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v hv => hv.1.trans hv.2)

end GlobalTheory.TripleAssembly
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.unitaryTypeLevelFamily_isOpen_le_latticeStabilizer : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  first | exact @GlobalTheory.TrIdem.levelFam_open_le | exact GlobalTheory.TrIdem.levelFam_open_le | (intros; apply GlobalTheory.TrIdem.levelFam_open_le <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.groupConvolution_normalizedIndicator_self : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  first | exact @GlobalTheory.TrIdem.conv_normInd_self | exact GlobalTheory.TrIdem.conv_normInd_self | (intros; apply GlobalTheory.TrIdem.conv_normInd_self <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.isRestrictedFiniteTensorFamily_typeIdempotents : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → U.u ∉ T.S → ∀ A, IsFinFamily D.sp.cm.sig V.gram (frameLat V) (fam T U μf A) := by
  first | exact @GlobalTheory.TrIdem.isFinFamily_fam | exact GlobalTheory.TrIdem.isFinFamily_fam | (intros; apply GlobalTheory.TrIdem.isFinFamily_fam <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

theorem _root_.GlobalTheory.T.smoothRepIntegratedOperator_normalizedIndicator_fixed : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth ρ → ∀ x : W, (∀ h ∈ H, ρ h x = x) → smoothOp ρ μ (normInd μ (H : Set G)) x = x := by
  first | exact @GlobalTheory.TrIdem.smoothOp_normInd_of_fixed | exact GlobalTheory.TrIdem.smoothOp_normInd_of_fixed | (intros; apply GlobalTheory.TrIdem.smoothOp_normInd_of_fixed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.mem_isotropicFlagParabolic_iff_splitPlaceChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.par hc (Fv F v) ↔ ∀ j, ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
  first | exact @GlobalTheory.SplitFlag.mem_par_iff_flagChain | exact GlobalTheory.SplitFlag.mem_par_iff_flagChain | (intros; apply GlobalTheory.SplitFlag.mem_par_iff_flagChain <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SplitFlag

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)}

theorem splitVec_sub' (τ : E →ₐ[F] Fv F v) (y z : Fin V.rank → Fv F v ⊗[F] E) :
    splitVec τ (y - z) = splitVec τ y - splitVec τ z := funext fun _ => map_sub _ _ _

variable (hc : Formalism.BasicNotions.CMData F E) (τ : E →ₐ[F] Fv F v)

theorem wPart_sub_of_mem_trivOn {A B : Submodule E V.V} {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (hg : g ∈ trivOn hc V (Fv F v) A B) {u : Fin V.rank → Fv F v} (hu : u ∈ wPart τ B) :
    (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨act hc V g y - y, hg.2 y hy, ?_⟩
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) = _
  rw [splitVec_sub', splitVec_matHom_mulVec]

variable (h : IsCMExt F E hc.sig) (hJ : IsHermND hc.sig V.gram)


include h hJ in
theorem mem_trivOn_of_wPart {A B : Submodule E V.V} (hAB : A ≤ B) {g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v}
    (h1 : ∀ u ∈ wPart τ B, (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ A)
    (h2 : ∀ u ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u - u ∈ wPart τ (perp V B))
    (h3 : ∀ u ∈ wPart τ (perp V A), ∃ u₀ ∈ wPart τ (perp V A), (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u) :
    g ∈ trivOn hc V (Fv F v) A B := by
  refine (mem_trivOn_iff_maps hAB).2 fun y hy => ?_
  rw [mem_extSub_iff_split hc h τ] at hy ⊢
  change splitVec τ ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _ ∧
    splitVec (τ.comp hc.sig) ((matHom _ hc.sig V.gram g).1 *ᵥ y - y) ∈ _
  rw [splitVec_sub', splitVec_sub', splitVec_matHom_mulVec, splitVec_matHom_mulVec]
  refine ⟨h1 _ hy.1, ?_⟩
  rw [mem_wPart_comp_iff hc h hJ τ]
  intro u hu
  obtain ⟨u₀, hu₀, rfl⟩ := h3 u hu
  have e := (mem_wPart_comp_iff hc h hJ τ).1 hy.2 _ (h2 u₀ hu₀)
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_eq_zero] at e
  rw [sub_dotProduct, pairing_splitHom, e, sub_self]

variable (𝔉 : IsoFlag V)

theorem flagChain_step_lo (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = i) :
    flagChain 𝔉 τ j.succ = wPart τ (𝔉.X i.succ) ∧ flagChain 𝔉 τ j.castSucc = wPart τ (𝔉.X i.castSucc) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_mid (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) = 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V 𝔉.top) ∧ flagChain 𝔉 τ j.castSucc = wPart τ 𝔉.top := by
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_le 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (𝔉.X a)) (Fin.ext (by simp <;> omega))

theorem flagChain_step_hi (i : Fin 𝔉.k) (j : Fin (2 * 𝔉.k + 1)) (hj : (j : ℕ) + i = 2 * 𝔉.k) :
    flagChain 𝔉 τ j.succ = wPart τ (perp V (𝔉.X i.castSucc)) ∧
      flagChain 𝔉 τ j.castSucc = wPart τ (perp V (𝔉.X i.succ)) := by
  have := i.2
  refine ⟨?_, ?_⟩
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))
  · rw [flagChain_of_lt 𝔉 τ (by simp <;> omega)]
    exact congrArg (fun a => wPart τ (perp V (𝔉.X a))) (Fin.ext (by simp <;> omega))

end GlobalTheory.SplitFlag


open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act) in
theorem GlobalTheory.SplitFlag.mem_unip_iff_flagChain : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  intro F E _ _ _ _ _ _ V v hc h hJ τ 𝔉 g
  constructor
  · intro hg j u hu
    simp only [IsoFlag.unip, Subgroup.mem_inf, Subgroup.mem_iInf] at hg
    obtain ⟨⟨hlo, hmid⟩, hhi⟩ := hg
    have := j.2
    rcases lt_trichotomy (j : ℕ) 𝔉.k with hj | hj | hj
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 ⟨j, hj⟩ j rfl
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hlo _) hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 j hj
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ hmid hu
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 ⟨2 * 𝔉.k - j, by omega⟩ j
        (show (j : ℕ) + (2 * 𝔉.k - j) = 2 * 𝔉.k by omega)
      rw [e1] at hu; rw [e2]; exact GlobalTheory.SplitFlag.wPart_sub_of_mem_trivOn hc τ (hhi _) hu
  · intro H
    have hstab : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        (splitHom hc.sig V.gram τ g).1 *ᵥ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j := by
      intro j u hu
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [GlobalTheory.SplitFlag.flagChain_zero, Submodule.mem_bot] at hu ⊢
        rw [hu, Matrix.mulVec_zero]
      · have := GlobalTheory.SplitFlag.flagChain_mono 𝔉 τ (Fin.castSucc_le_succ j') (H j' u hu)
        simpa using add_mem this hu
    have hsurj : ∀ j : Fin (2 * 𝔉.k + 2), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j,
        ∃ u₀ ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j, (splitHom hc.sig V.gram τ g).1 *ᵥ u₀ = u :=
      fun j u hu => GlobalTheory.SplitFlag.exists_mulVec_eq_of_maps _ _ (hstab j) u hu
    rw [IsoFlag.mem_unip]
    refine ⟨fun i => ?_, ?_⟩
    · have := i.2
      obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_lo τ 𝔉 i ⟨i, by omega⟩ rfl
      obtain ⟨e3, e4⟩ := GlobalTheory.SplitFlag.flagChain_step_hi τ 𝔉 i ⟨2 * 𝔉.k - i, by omega⟩
        (show 2 * 𝔉.k - (i : ℕ) + i = 2 * 𝔉.k by omega)
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ (𝔉.le_succ i) ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [← e3, ← e4]; exact H _
      · rw [← e3]; exact hsurj _
    · obtain ⟨e1, e2⟩ := GlobalTheory.SplitFlag.flagChain_step_mid τ 𝔉 ⟨𝔉.k, by omega⟩ rfl
      refine GlobalTheory.SplitFlag.mem_trivOn_of_wPart hc τ h hJ 𝔉.iso ?_ ?_ ?_
      · rw [← e1, ← e2]; exact H _
      · rw [GlobalTheory.SplitFlag.perp_perp, ← e1, ← e2]; exact H _
      · rw [← e1]; exact hsurj _
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau)
  (B g₀' : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v₀ : M.H τ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (M.ε τ) * B = gramAt D V τ → g₀' ∈ Formalism.MainNotions.S.UJset (M.ε τ) →
  B⁻¹ * g₀' * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧
  ∀ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), GlobalTheory.PackLoc.mco M τ (B⁻¹ * g₀' * M.fr τ) v₀ x =
    ⟪M.σ τ g₀' v₀, M.σ τ (B * x * B⁻¹) (M.σ τ g₀' v₀)⟫_ℂ := by
  first | exact @GlobalTheory.PackLoc.mco_frame | exact GlobalTheory.PackLoc.mco_frame | (intros; apply GlobalTheory.PackLoc.mco_frame <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel Y S) (τ : D.what₂.Tau),
  (∀ u : Formalism.REAL.UJ (M.ε τ), GlobalTheory.PackLoc.ptY M τ u ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
    (GlobalTheory.ConjDS.conjModel M).fr τ * GlobalTheory.PackLoc.ptY M τ u * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
      GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u) ∧
    M.rep τ (GlobalTheory.PackLoc.ptY M τ u) = M.σ τ (Formalism.MainNotions.S.umat u)) ∧
  ∀ X ∈ lieAt Y τ,
    (GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ ∈
      GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M).ε τ)) ∧
    ∀ s : ℝ, cmp θ τ (oneP θ Y τ X s) ∈ Formalism.QuantumDeterminants.UH (gramAt D Y τ) ∧
      (GlobalTheory.ConjDS.conjModel M).fr τ * cmp θ τ (oneP θ Y τ X s) * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹ =
        NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M).fr τ * X * ((GlobalTheory.ConjDS.conjModel M).fr τ)⁻¹)) := by
  first | exact @GlobalTheory.PackLocFacts.frame_facts | exact GlobalTheory.PackLocFacts.frame_facts | (intros; apply GlobalTheory.PackLocFacts.frame_facts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (A : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (K lam q : ℝ) (c : ℂ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, ∀ (s : ℝ) u,
    GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • (A * X * A⁻¹)) * GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ X ∈ lieAt Y τ, A * X * A⁻¹ ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ((GlobalTheory.ConjDS.conjModel M₀).ε τ)), ∀ s : ℝ,
    Integrable (fun h => ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (NormedSpace.exp (s • X) * Formalism.MainNotions.S.umat h)) v⟫_ℂ -
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
        K * |s| * GlobalTheory.SepReal.hsn X) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ,
    (Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) ∧
    ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
      lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < lam → lam * K ≤ Real.exp q * ‖c‖ →
  ∀ X ∈ lieAt Y τ, ∀ s : ℝ,
    Integrable (fun u => ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖) (Formalism.REAL.muG (M₀.ε τ)) ∧
    ∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (cmp θ τ (oneP θ Y τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) -
      GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ)) ≤
      Real.exp q * ‖c‖ * |s| * hsn (A * X * A⁻¹) := by
  first | exact @GlobalTheory.PackLoc.lipAt | exact GlobalTheory.PackLoc.lipAt | (intros; apply GlobalTheory.PackLoc.lipAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.transversal_coefficient_decay_at_real_place : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c₁ lam q Cb : ℝ) (k : ℕ),
  IsUnit B → Bᴴ * Formalism.REAL.Jm (MP.ε τ) * B = gramAt D V τ → B *ᵥ (fun i => tauE D τ (zv d i)) = Pi.single (e none) 1 →
  V.rank = k + 1 →
  (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ,
    Integrable (fun u : Formalism.REAL.UJ (M₀.ε τ) => F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) (Formalism.REAL.muG (M₀.ε τ)) ↔
      Integrable (fun h => F (Formalism.MainNotions.S.umat h)) (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℝ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  0 < c₁ → 0 < lam → Cb ≤ Real.exp q →
  (∀ g ∈ Formalism.MainNotions.S.UJset (MP.ε τ),
    Integrable (fun h => ⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
      (Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ∧
    ∫ h, ‖⟪v, MP.σ τ (g * GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) ≤
      c₁ * Cb * Real.sqrt (∑ a, ‖g a (e none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) →
  ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    Integrable (fun u => GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)))
      (Formalism.REAL.muG (M₀.ε τ)) ∧
    (∫ u, ‖GlobalTheory.PackLoc.mco MP τ g₀ v₀ (g * GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u))‖ ∂(Formalism.REAL.muG (M₀.ε τ))) *
      eu (B *ᵥ (g *ᵥ fun i => tauE D τ (zv d i))) ^ (2 * V.rank + 5) ≤ Real.exp q * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
  first | exact @GlobalTheory.PackLoc.farClause | exact GlobalTheory.PackLoc.farClause | (intros; apply GlobalTheory.PackLoc.farClause <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

theorem _root_.GlobalTheory.T.no_invariant_pairing_smaller_fock_discreteSeries : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK → NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ b : Formalism.BasicNotions.TH.Pol (p - i) (q - i) r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq r s, ∀ P y, b (fockAct2 (p - i) (q - i) r s Z P) y + b P ((X.ds r s lam').HK.act Z y) = 0) → b = 0 := by
  first | exact @GlobalTheory.NoLowPairing.no_pairing_of_noLow | exact GlobalTheory.NoLowPairing.no_pairing_of_noLow | (intros; apply GlobalTheory.NoLowPairing.no_pairing_of_noLow <;> assumption)
end
