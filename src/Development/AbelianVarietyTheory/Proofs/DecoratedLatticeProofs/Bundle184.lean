module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle057
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle064
import Formalism.LocalToGlobal.Columns.ChainTwAn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle162
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem holValueAt_eq_div_mul : ∀ (Z L d Y : ℂ → ℂ) (s₀ z l : ℂ) (s₁ : ℝ), 0 < s₀.re → s₁ < s₀.re → AnalyticOnNhd ℂ d (rightOf 0) → (∀ s : ℂ, 0 < s.re → d s ≠ 0) → DifferentiableOn ℂ Y (rightOf s₁) → EqRight Z (fun s => L s / d s * Y s) → HolValueAt Z s₀ z → HolValueAt L s₀ l → z = l / d s₀ * Y s₀ := by
  intro Z L d Y s₀ z l s₁ h0 h1 hd hd0 hY e hZ hL
  exact (hZ.congr e).unique ((hL.div (holValueAt_self hd h0) (hd0 _ h0)).mul
    (holValueAt_self (hY.analyticOnNhd (isOpen_rightOf s₁)) h1))

end GlobalTheory.Core.Rk.IP
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOntoSph

variable {D : D7}


open Classical in
theorem sep_level {c : Com D} {j : ℕ} {s : PiLocalization₂ D} (hs : s.Is c j) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : OffS D c.S P) : ∀ PP, PP ∈ s.L.Pg ∨ PP ∈ s.L.Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
  obtain ⟨hr, ξ, hL⟩ := hs.lev
  have hPg : s.L.Pg = c.Pg := by rw [hL]; rfl
  have hQ : s.L.Q = ∅ := by rw [hL]; rfl
  rintro PP (h | h)
  · rw [hPg] at h
    exact GlobalTheory.HeckeOffLevel.sep_of_offS hP (by unfold Com.S; exact Finset.mem_image.2 ⟨PP, h, rfl⟩)
  · rw [hQ] at h
    exact absurd h (Finset.notMem_empty _)

theorem exists_unif_of_F (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E, (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧
      y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  haveI := P.isPrime
  haveI : Algebra.IsUnramifiedAt (𝓞 D.host.F) P.asIdeal :=
    Algebra.unramified_iff_forall.1 (GlobalTheory.InertOfConj.unram D) ⟨P.asIdeal, P.isPrime⟩
  have hle : (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal :=
    Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff P.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 D.host.F) (P.asIdeal.under (𝓞 D.host.F)) P.asIdeal).1 ‹_›).2
  have h2 : ¬ (P.asIdeal.under (𝓞 D.host.F)).map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ P.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  rw [Ideal.map_le_iff_le_comap] at h2
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.1 h2
  exact ⟨x, algebraMap _ _ x, rfl, Ideal.mem_comap.1 hx, fun h => hx2 (Ideal.mem_comap.2 h)⟩

theorem level_spherical_off_S : ∀ D : D7, ForStage D fun c _ s => SphOff (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S ∧
    SphOff (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S ∧
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, OffS D c.S P → IsPrimeIdem P e f → ∀ k ∈ Lev.levG s.V s.β s.L,
      ∃ k₁ ∈ Lev.levG s.V s.β s.L, ∃ k₂ ∈ Lev.levG s.V s.β s.L, SuppF s.V f k₁ ∧ SuppF s.V (1 - f) k₂ ∧ k = k₁ * k₂) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S) ∧
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ x : 𝓞 D.host.F, ∃ y : 𝓞 D.host.E,
      (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2 := by
  intro D c _ j _ s hs
  obtain ⟨N, hB, hNP⟩ := hs.base
  have hoff : ∀ P, OffS D c.S P ↔ P.under (𝓞 D.host.F) ∉ c.S := fun P => GlobalTheory.GoodPrimes.offS_iff _ P
  have key := fun P e f (hP : OffS D c.S P) (hi : IsPrimeIdem P e f) =>
    (GlobalTheory.LevSplit.lev_split s.V s.β s.Λ N s.L hB).2 P e f hi (hNP P ((hoff P).1 hP)) (sep_level hs hP)
  have hex := fun P => (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents s.V).2.1 P
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P e f hP hi => (key P e f hP hi).2.2, hoff, exists_unif_of_F⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    exact ⟨e, f, hi, h1, h2⟩
  · obtain ⟨e, f, hi⟩ := hex P
    obtain ⟨h1, h2, -⟩ := key P e f hP hi
    refine ⟨e, f, hi, h1, fun g hg hf => ?_⟩
    show conj (Lev.levChi s.V s.β s.L g) = 1
    rw [h2 g hg hf, map_one]

end GlobalTheory.ChainOntoSph

end
end

section

noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SatCompare
open Formalism.MainNotions.SchurIrreducible (IsSplit)

section GLcase
variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x x' : V}
  {B : Multiset ℂˣ}

theorem satGL_add (hx : IsSatVecGL w ρ x B) (hx' : IsSatVecGL w ρ x' B) (h0 : x + x' ≠ 0) :
    IsSatVecGL w ρ (x + x') B :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    have e := (heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2.2 ϖ hϖ j hj, hx'.2.2.2 ϖ hϖ j hj, smul_add]⟩

theorem satGL_smul (hx : IsSatVecGL w ρ x B) {a : ℂ} (ha : a ≠ 0) : IsSatVecGL w ρ (a • x) B :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, hx.2.2.1, fun ϖ hϖ j hj => by
    rw [_root_.GlobalTheory.LFun.SatCompare.heckeVec_smul (Final.GLintComm E w n) (Tj_mem_hecke hϖ j), hx.2.2.2 ϖ hϖ j hj, smul_comm]⟩

end GLcase

section Ucase
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ϖ : L} {q : ℕ} {ρ : Representation ℂ (GU c n) V} {x x' : V}
  {α : Fin (n / 2) → ℂˣ}

theorem satU_add (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) (hx' : IsSatVecU ϖ q ρ x' α) (h0 : x + x' ≠ 0) :
    IsSatVecU ϖ q ρ (x + x') α :=
  ⟨h0, add_mem hx.2.1 hx'.2.1, fun t ht => by
    have e := (heckeLin (P.isCommensurated_integral_unitary_of_unramified hU n) ht ρ).map_add x x'
    simp only [heckeLin_apply] at e
    rw [e, hx.2.2 t ht, hx'.2.2 t ht, smul_add]⟩

theorem satU_smul (hU : IsUnramInv ϖ c q) (hx : IsSatVecU ϖ q ρ x α) {a : ℂ} (ha : a ≠ 0) :
    IsSatVecU ϖ q ρ (a • x) α :=
  ⟨smul_ne_zero ha hx.1, Submodule.smul_mem _ a hx.2.1, fun t ht => by
    rw [_root_.GlobalTheory.LFun.SatCompare.heckeVec_smul (P.isCommensurated_integral_unitary_of_unramified hU n) ht, hx.2.2 t ht, smul_comm]⟩

end Ucase

section Vec
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {x x' : V} {B : Multiset ℂˣ}

theorem paramVec_smul (hx : IsParamVec σ J L h ρ x B) {a : ℂ} (ha : a ≠ 0) : IsParamVec σ J L h ρ (a • x) B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_smul hx ha⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, satU_smul hU hx ha, hB⟩

theorem paramVec_add (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x' B) (h0 : x + x' ≠ 0) :
    IsParamVec σ J L h ρ (x + x') B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, satGL_add hx (hx'.isSatVecGL hv he) h0⟩
  · rcases hx' with ⟨hv, -⟩ | ⟨-, c', ϖ', e', α', hU', he', hx', hB'⟩
    · exact absurd hv (not_isSplit_of_isInertAt hw)
    · obtain rfl : c' = c := (InertChart.existsUnique_isConjAt σ hw h).unique he'.1 he.1
      have h1 := IsSatVecU.of_unif hU' hU (IsSatVecU.of_chart he' he hx')
      have h2 : IsSatVecU ϖ (qV F v) (ρ.comp e.symm.toMonoidHom) x' α := ⟨h1.1, h1.2.1, fun t ht => by
        rw [h1.2.2 t ht, GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq (w.adicCompletion E) ϖ c' (qV F v) n hU α' α (hB'.symm.trans hB) t ht]⟩
      exact Or.inr ⟨hw, c', ϖ, e, α, hU, he, satU_add hU hx h2 h0, hB⟩

end Vec

end GlobalTheory.LFun.ParLin

noncomputable section

namespace GlobalTheory.LFun.ParLin

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

section Fun
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V] {f f' : GAd σ J → V} {B B' : Fam E}

theorem paramFun_of_agree (hf : IsParamFun σ J L S f B') (hB : ∀ w ∉ above E S, B w = B' w) :
    IsParamFun σ J L S f B := fun v hv w h => by
  have hw : w ∉ above E S := fun hm => hv (h ▸ hm)
  rw [hB w hw]
  exact hf v hv w h

theorem paramFun_add (hf : IsParamFun σ J L S f B) (hf' : IsParamFun σ J L S f' B) (h0 : f + f' ≠ 0) :
    IsParamFun σ J L S (f + f') B := fun v hv w h => paramVec_add (hf v hv w h) (hf' v hv w h) h0

theorem paramFun_smul (hf : IsParamFun σ J L S f B) {a : ℂ} (ha : a ≠ 0) : IsParamFun σ J L S (a • f) B :=
  fun v hv w h => paramVec_smul (hf v hv w h) ha

end Fun

end GlobalTheory.LFun.ParLin

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LFun.ParLin in
theorem isPar_add_smul : ∀ (D : D7) (c : Com D) (s : PiLocalization₂ D), (∀ (u u' : s.CC c) B B' (a : ℂ), IsPar u B → IsPar u' B' →
    (∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), B w = B' w) →
    u + a • u' ≠ 0 → IsPar (u + a • u') B) ∧ ∀ (u : s.CC c) B (a : ℂ), IsPar u B → a ≠ 0 → IsPar (a • u) B := by
  intro D c s
  have cne : ∀ f : GA D s.V → ℂ, f ≠ 0 → (fun g => conj (f g)) ≠ 0 := fun f hf h0 =>
    hf (funext fun g => by simpa using congrFun h0 g)
  refine ⟨fun u u' B B' a hu hu' hB h0 => ⟨h0, fun v hv => ?_⟩, fun u B a hu ha => ⟨smul_ne_zero ha hu.1, fun v hv => ?_⟩⟩
  · have hval : PiLocalization₂.val (u + a • u') v = PiLocalization₂.val u v + a • PiLocalization₂.val u' v := by simp [PiLocalization₂.val]
    have hc : (fun g => conj (PiLocalization₂.val (u + a • u') v g)) =
        (fun g => conj (PiLocalization₂.val u v g)) + (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    by_cases h1 : PiLocalization₂.val u v = 0
    · have h2 : a • PiLocalization₂.val u' v ≠ 0 := by rw [hval, h1, zero_add] at hv; exact hv
      have ha : a ≠ 0 := fun e => h2 (by simp [e])
      have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
      have hz : (fun g => conj (PiLocalization₂.val u v g)) = 0 := by funext g; simp [h1]
      rw [hz, zero_add]
      exact paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)
    · by_cases h2 : a • PiLocalization₂.val u' v = 0
      · have hz : (conj a) • (fun g => conj (PiLocalization₂.val u' v g)) = 0 := by
          funext g
          have := congrFun h2 g
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
          rw [← map_mul, this, map_zero]
        rw [hz, add_zero]
        exact hu.2 v h1
      · have ha : a ≠ 0 := fun e => h2 (by simp [e])
        have hu'v : PiLocalization₂.val u' v ≠ 0 := fun e => h2 (by simp [e])
        refine paramFun_add (hu.2 v h1) (paramFun_smul (paramFun_of_agree (hu'.2 v hu'v) hB) (by simpa using ha)) ?_
        rw [← hc]
        exact cne _ hv
  · have hval : PiLocalization₂.val (a • u) v = a • PiLocalization₂.val u v := by simp [PiLocalization₂.val]
    have hu0 : PiLocalization₂.val u v ≠ 0 := fun e => hv (by rw [hval, e, smul_zero])
    have hc : (fun g => conj (PiLocalization₂.val (a • u) v g)) = (conj a) • (fun g => conj (PiLocalization₂.val u v g)) := by
      funext g; simp [hval]
    unfold ParFun
    rw [hc]
    exact paramFun_smul (hu.2 v hu0) (by simpa using ha)

end GlobalTheory.ChainOnto
end
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjVal

variable {D : D7}

def Good (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (f : GA D V → ℂ) : Prop :=
  Continuous f ∧ (∃ C : ℝ, ∀ g, ‖f g‖ ≤ C) ∧ (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) ∧ ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g

theorem Good.add {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f f' : GA D V → ℂ}
    (h : Good V J χ f) (h' : Good V J χ f') : Good V J χ (f + f') := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  obtain ⟨c', ⟨C', hC'⟩, l', r'⟩ := h'
  refine ⟨c.add c', ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩,
    fun γ hγ g => by simp [l γ hγ g, l' γ hγ g], fun k hk g => by simp [r k hk g, r' k hk g, mul_add]⟩

theorem Good.smul {V : HSp D} {J : Set (GA D V)} {χ : GA D V → ℂ} {f : GA D V → ℂ} (a : ℂ)
    (h : Good V J χ f) : Good V J χ (a • f) := by
  obtain ⟨c, ⟨C, hC⟩, l, r⟩ := h
  refine ⟨continuous_const.mul c, ⟨‖a‖ * C, fun g => ?_⟩,
    fun γ hγ g => by simp [l γ hγ g], fun k hk g => by simp [r k hk g, mul_left_comm]⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg a)

theorem good_val (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D}
    {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    (u : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) (hu : u ∈ MultT θ M J χ) (v : ⨂[ℂ] τ, M.sm τ) :
    Good V J χ (u v) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT θ M J χ u).1 hu)
  have hu' : u = PiTensorProduct.lift (PiTensorProduct.lift.symm u) := (LinearEquiv.apply_symm_apply _ _).symm
  induction v using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    rw [map_smul]
    refine Good.smul a ?_
    rw [hu', PiTensorProduct.lift.tprod]
    exact ⟨(hT.aut x).cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hT.aut x) (hT.cusp x), (hT.aut x).left,
      hT.lev x⟩
  | add x y hx hy =>
    rw [map_add (f := _)]
    exact hx.add hy

theorem conj_eq_one_iff' (z : ℂ) : conj z = 1 ↔ z = 1 := by
  constructor
  · intro h; simpa using congrArg conj h
  · intro h; simp [h]

theorem conj_values_hecke : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ForStage D fun c _ s =>
    (∀ (u : s.CC c) v, Continuous (PiLocalization₂.val u v) ∧ (∃ C : ℝ, ∀ g, ‖PiLocalization₂.val u v g‖ ≤ C) ∧
      (∀ γ ∈ GQ s.V, ∀ g, PiLocalization₂.val u v (γ * g) = PiLocalization₂.val u v g) ∧
      ∀ k ∈ levS s.V s.β s.L, ∀ g, PiLocalization₂.val u v (g * k) = Lev.levChi s.V s.β s.L k * PiLocalization₂.val u v g) ∧
    (∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R ↔
      Hecke₂ s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S P d R) ∧
    ∀ (R : Finset (GA D s.V)) (f : GA D s.V → ℂ),
      heckeLin s.V R (fun g => conj (f g)) = fun g => conj (heckeLin s.V R f g) := by
  intro hP D c hc j _ s _
  refine ⟨fun u v => good_val hP hc.inf (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) u.2 v, fun P d R => ?_, fun R f => ?_⟩
  · simp only [Hecke₂, conj_eq_one_iff']
  · funext g

    simp [heckeLin, map_sum]

end GlobalTheory.ConjVal

end
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwSumAgree

theorem sumAgree : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hok hAt
  have hPA := GlobalTheory.T.parahoric_test_functions_agree_rational_points X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hok hAt
  have hiL := GlobalTheory.Proof.TwistSupportPeriodicLevels.ofTwist_support_periodic_levels k s (Fin R.k ⊕ Fin (s + 1)) (Fin R.t)
    (Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2)) (XIx (Fin R.k) (Fin R.t)) W.δ W.tame W.η
    (fun j c h => GlobalTheory.StepData.plainFrame (stdOrd (Fin R.k) (Fin R.t) j c h)) (LatFrame.refl k _) (fun _ _ _ => rfl)
  intro j c h a b g g' hag hbg' ha hb hD
  have hm := hAt.steps
  refine ⟨j + 1, j + 1, fun A' B' hA hB e' e hoe' hoe x => ?_⟩
  obtain ⟨E', hE', hg⟩ := id hag
  obtain ⟨E, hE, hg'⟩ := id hbg'
  have hj : j < R.m := by omega
  have hom := GlobalTheory.TwBridge.Model.om_agree Ch sel mu cst σ₀ P ι s W hAt hok j (c + 1) (c + 1 + 1) hj E' E a b g g' hg hg'
    ((W.T s R).Phi j (c + 1) (by omega)) (PhiAt Ch mu cst.sharp j P.1)
    (fun y => hPA.1 j (c + 1) (by omega) E' E hE' hE y)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl j (c + 1 + 1) a g hag ha
  obtain ⟨h1', h2'⟩ := GlobalTheory.T.completionMatrix_boundedRationalAut_integral ι W.ϖ P.1 hAt.nmem hAt.compl (j + 1) (c + 1) b g' hbg' hb
  have hSP := GlobalTheory.T.linearWeilAction_support_and_period_integral W.ϖ ((W.unif W.ϖ).2 le_rfl) j ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega))
    (hiL.1 j (c + 1) (by omega)) (hiL.2.1 j (c + 1) (by omega)) g g' h1 h2 h1' h2'
  have hpsi : ∀ z, IntAt P.1 ((qOf P.1 : X.E) ^ (j + 1) * z) → (W.ψ (ι z) : ℂ) = σ₀ (cst.psi P z) :=
    fun z hz => hAt.psi z (twAn_qpow_mul (by omega) hz)
  have o1 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e' z).val) (R.N j)) E' := by
    rintro (z | z)
    · exact (hE' _).trans (hoe' z).symm
    · exact hE' _
  have o2 : GlobalTheory.SymBridge.IsOrd (GlobalTheory.SymBridge.yPos (fun z => (e z).val) (R.N (j + 1))) E := by
    rintro (z | z)
    · exact (hE _).trans (hoe z).symm
    · exact hE _
  exact GlobalTheory.T.unfoldingIntegral_positionOne_eq_finite_sum X.E X.K k P.1 (qOf P.1) ι W.ϖ σ₀ W.ψ ν (cst.psi P) (j + 1) hAt.compl W.unif W.cond hν hpsi
    (XIx (Fin R.k) (Fin R.t) j) (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) (R.N j) (cOf R j) (R.N (j + 1)) (cOf R (j + 1))
    A' B' (by omega) (by unfold cOf; omega) (by unfold cOf; omega) hA hB e' e E' E o1 o2 _ _ _ hom hSP.1 hSP.2 x

end GlobalTheory.TwSumAgree
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.doubleLiftPeriod_rankZero_fubini_compactQuotient : ∀ D : D7, LastLaw D := by
  first | exact @GlobalTheory.Unf.LastSteps.lastLaw | exact GlobalTheory.Unf.LastSteps.lastLaw | (intros; apply GlobalTheory.Unf.LastSteps.lastLaw <;> assumption)
end

section

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix

theorem _root_.GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧ (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧ ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  intro Λ hΛ
  have := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

theorem _root_.GlobalTheory.T.completion_tensor_relativeBasis_coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) → ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 := by
  first | exact @GlobalTheory.CoordUnique.coords_unique | exact GlobalTheory.CoordUnique.coords_unique | (intros; apply GlobalTheory.CoordUnique.coords_unique <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.FinPl
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_adele_supportedAt_place_not_integral : ∀ (D : D7) (v : Pl D), ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.NotIntAt.exists_not_intAt | exact GlobalTheory.FinPl.NotIntAt.exists_not_intAt | (intros; apply GlobalTheory.FinPl.NotIntAt.exists_not_intAt <;> assumption)
end
