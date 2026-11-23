module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle904
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle880
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle804
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle839
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle758
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle659
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle449
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle822
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle415
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle905
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle906
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle879
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle910
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle897
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle566
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLocalGenerationSplitPlaceOffLevels
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaShapeRelationDropSplitPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle699
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TheoremT




theorem liftF_of_isGood : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  intro hBS hFon l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hNum T₁ T₂ g hg hG₁ hG₂
  have hN2 := hNum.two_le
  have hlarge := hNum.large
  have hHN : 4 * H ≤ H * N ^ 2 := by
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H h4
  have hl2 : l ≠ 2 := by intro h; subst h; nlinarith
  have h8 : 8 * H + 1 < l := by nlinarith
  obtain ⟨T₀, f, hSES, hG₀⟩ := GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice hFon l a e ϖ LL Pl AI hStd Sig U T₁ T₂ g hg hG₁
  obtain ⟨P₀, -⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₀ hG₀
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₁ hG₁
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₂ hG₂
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₀ T₁ P₀ P₁ f
  obtain ⟨G, hG⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₁ T₂ P₁ P₂ g
  have hEx := GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL (Fin P₀.n) (Fin P₁.n) (Fin P₂.n) P₀.D.toPhiMod P₁.D.toPhiMod
    P₂.D.toPhiMod T₀ T₁ T₂ P₀.R.I P₁.R.I P₂.R.I f g F.toHom G.toHom hSES hF hG
  have hAdm : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.Admissible l e N η H Sig U :=
    ⟨hNum.frob_mem, hNum.zero_mem_Sig, hNum.card_Sig, hNum.two_le, hNum.range_U, hNum.zero_mem_U,
      hNum.card_U, hNum.one_le, hNum.lt, hNum.large⟩
  have hpot₂ := GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ (Fin P₂.n) η H P₂.D T₂ P₂.R
  unfold LatHom.LiftF
  intro c hc

  obtain ⟨y₂, hy₂, hMon₂, hCl₂⟩ :=
    GlobalTheory.T.crystalline_class_from_monodromy_kernel_element hBS hFon l a e ϖ LL Pl AI hStd N η H Sig U hNum T₂ hG₂ P₂ c hc

  obtain ⟨y₂', hy₂', m₂, hm₂, hsum⟩ :=
    Submodule.mem_sup.1 ((GlobalTheory.T.prime_pow_divisibility_of_descentDatum _ _ l e a _ η H P₂.D).2 y₂ hy₂)
  have hrew : y₂' + P₂.D.phi m₂ = (l : ↥LL.1) ^ η • y₂ + (P₂.D.phi m₂ - m₂) := by
    rw [← hsum]; abel
  have hMon₂' : P₂.D.Mon (y₂' + P₂.D.phi m₂) = 0 := by
    rw [hrew, P₂.D.Mon_add_phi_sub _ (PhiMod.M_le_Man _ hm₂.1), LinearMap.map_smul, hMon₂, smul_zero]
  have hCl₂' : P₂.R.ClassOf (y₂' + P₂.D.phi m₂)
      ((l : ↥LL.1) ^ η • (l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
    rw [hrew]
    exact hpot₂.2.2.2 _ _ m₂ hm₂ (hpot₂.2.2.1 _ _ η hCl₂)

  obtain ⟨y', hy', m, hm, hMon, hGy⟩ :=
    GlobalTheory.T.liftingTheorem_phiModules_exact_triple _ _ l e a _ _ _ η H P₀.D P₁.D P₂.D F G N Sig U
      ⟨hEx, hNum, hP₁, hP₂.chars_subset⟩ y₂' hy₂' m₂ hm₂ hMon₂'

  have hζ := GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice _ _ l e a _ N η H Sig U hAdm P₁.D hP₁ y' hy' m hm hMon
  obtain ⟨κ₁, hκ₁, hCl₁⟩ := GlobalTheory.T.galoisClass_of_monodromy_eq_zero hFon l a e ϖ LL (Fin P₁.n) η H P₁.D T₁ P₁.R Pl AI hStd hNum.lt h8
    _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.add_phi_mem_Y hy' hm) hMon _ hζ

  have hnat := GlobalTheory.T.tame_breuil_kisin_datum_exists l a e _ _ (thetaW a LL) ϖ (Fin P₁.n) (Fin P₂.n) η H P₁.D P₂.D T₁ T₂ P₁.R P₂.R g G hG
    _ _ hCl₁
  have happ : G.app ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig • (y' + P₁.D.phi m)) =
      (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) •
        (y₂' + P₂.D.phi m₂) := by
    have happ0 : ∀ (k : ↥LL.1) (v : Vec (↥LL.1) a (Fin P₁.n)), G.app (k • v) = k • G.app v := by
      intro k v
      ext1 τ
      simp only [Hom.app_apply, Pi.smul_apply, Matrix.mulVec_smul]
    rw [happ0, hGy, smul_smul, ← pow_add]
  rw [happ] at hnat
  have hCl := hpot₂.2.2.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) hCl₂'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hCl
  have hB := hpot₂.2.1 _ _ _ hnat hCl

  have hexp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) ≤ 7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁,
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    generalize maxPeriod l Sig = r
    have h1 : n + 2 - 1 = n + 1 := by omega
    rw [h1]
    nlinarith [Nat.zero_le (n * r), Nat.zero_le (η * n), Nat.zero_le (η * r)]
  rw [← algebraMap_smul (↥LL.1), map_pow, map_natCast, Pl.PD_p,
    ← Nat.sub_add_cancel hexp, pow_add, mul_smul]
  obtain ⟨β, hβ, hβeq⟩ : ∃ β ∈ latticeCoboundaries T₂.L, (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig)) • c = LatHom.post g κ₁ - β := ⟨_, hB, by abel⟩
  rw [hβeq, smul_sub]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hκ₁)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hβ

end GlobalTheory.TheoremT
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SeriesTie

theorem _root_.GlobalTheory.T.artinMap_splitPlaceUniformiser_eq_frobenius_inv : ∀ (D : D7) (Ω : Type) [Field Ω] [Algebra D.host.E Ω] (A : Type) [CommGroup A] (a : Recip D Ω), a.Good → ∀ φ : G D.host.E Ω →* A, IsOpen (φ.ker : Set (G D.host.E Ω)) → ∀ (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ B : ValuationSubring Ω, IsPlaceOver B P → (∀ τ ∈ Ine (F := D.host.E) B, φ τ = 1) → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) B (normV P) σ → a.pull φ x = (φ σ)⁻¹ := by
  first | exact @GlobalTheory.SeriesTie.Recip.pull_locUnif | exact GlobalTheory.SeriesTie.Recip.pull_locUnif | (intros; apply GlobalTheory.SeriesTie.Recip.pull_locUnif <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.residue_character_artin_tame_galois_eq_tame_value : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (rc : Recip D D.nd.Om), rc.Good → ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (φ : G D.host.E D.nd.Om →* Rˣ), IsOpen (φ.ker : Set (G D.host.E D.nd.Om)) → ∀ (PP : Pl D.host.E) (m : ℕ), ((m : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A PP → ∀ σ ∈ Ine (F := D.host.E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1) → Formalism.L2.NTheta.IsIdemAt (idemAt PP) PP → ∀ c : (kP PP)ˣ →* Circle, IsResAt (GlobalTheory.SeriesTie.charOf rc f φ) PP c → ∀ (e : ℤ) (u : 𝓞 D.host.E), u ∉ PP.asIdeal → ∀ z : (kP PP)ˣ, (z : kP PP) = Ideal.Quotient.mk PP.asIdeal u → ((c z : Circle) : ℂ) ^ e = f (NX.tameVal φ PP e u).1 := by
  first | exact @GlobalTheory.TameResRead.res_zpow_eq_tameVal | exact GlobalTheory.TameResRead.res_zpow_eq_tameVal | (intros; apply GlobalTheory.TameResRead.res_zpow_eq_tameVal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.artin_twisting_character_delta_good : ∀ (D : D7) (a : Recip D D.nd.Om), a.Good → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → ∀ (f : D.ntw.O0 i →+* ℂ), Function.Injective f → ∀ b : Bool, (twistOf a f ch (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))).Good := by
  first | exact @GlobalTheory.DeltaGood.twistOf_delta_good | exact GlobalTheory.DeltaGood.twistOf_delta_good | (intros; apply GlobalTheory.DeltaGood.twistOf_delta_good <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms



theorem hecke_geo {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hsp : HEq D.sp D'.sp)
    (j : Fin D.R.m) (j' : Fin D'.R.m) (hj : (j : ℕ) = j') :
    GA D (Wc D j) = GA D' (Wc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧
    ∀ (β : GL (Fin (Wc D j).rank) (Lev.EAf D)) (β' : GL (Fin (Wc D' j').rank) (Lev.EAf D')), HEq β β' →
    ∀ (Pg : Finset (Pl D.host.E)) (Pg' : Finset (Pl D'.host.E)), HEq Pg Pg' →
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ (k : ℕ) (α' : GA D' (Wc D' j')) (R' : Finset (GA D' (Wc D' j'))),
      IsHeckeAt (Wc D' j') P' k α' →
      Bridge.IsDC (Lev.levG (Wc D' j') β' (Lev.datY _ D'.R.r D'.R.t 0 (r_le_rank_Wc j') Pg' ∅ (LevelP.triv _ _ _)
        (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α' R' →
      ∃ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α ∧
        Bridge.IsDC (Lev.levG (Wc D j) β (Lev.datY _ D.R.r D.R.t 0 (r_le_rank_Wc j) Pg ∅ (LevelP.triv _ _ _)
          (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α R ∧
        ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' j') R' F') := by
  cases D; cases D'
  dsimp only at hR hH hsp
  subst hR; subst hH; subst hsp
  cases Fin.ext hj
  refine ⟨rfl, HEq.rfl, fun β β' hβ Pg Pg' hPg P P' hP k α R h1 h2 => ?_⟩
  subst hβ; subst hPg; subst hP
  exact ⟨α, R, h1, h2, fun F F' hF => by subst hF; rfl⟩



theorem exists_sameVec {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hT : D.what₂.Tau = D'.what₂.Tau)
    (he : HEq D.eTau D'.eTau) {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar} {P' : D'.what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (hM : SameModel M M') (v' : M'.Vec) : ∃ v : M.Vec, SameVec v v' := by
  obtain ⟨h1, h2, h3, h4, -, -, h5⟩ := hM
  obtain ⟨R, H, sp, vol, vp, what₂, eT⟩ := D
  obtain ⟨R', H', sp', vol', vp', rows', eT'⟩ := D'
  dsimp only at hR hH hT he
  subst hR; subst hH
  cases what₂; cases rows'
  dsimp only at hT he
  subst hT; subst he; subst hV
  cases M; cases M'
  dsimp only at h1 h2 h3 h4 h5
  subst h1; subst h2; subst h3; subst h4; subst h5
  exact ⟨v', fun τ τ' h => by subst h; rfl⟩



theorem place_geo {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') :
    PlE H = PlE H' ∧ ∀ (P : PlE H) (P' : PlE H'), HEq P P' → (IsSplitPl H P ↔ IsSplitPl H' P') ∧
      Nat.card (kP P) = Nat.card (kP P') ∧
      (∀ (χ : Formalism.L2.Host.HChar H.E) (χ' : Formalism.L2.Host.HChar H'.E), HEq χ χ' → χ.val P = χ'.val P') := by
  subst hR; subst hH
  refine ⟨rfl, fun P P' hP => ?_⟩
  subst hP
  exact ⟨Iff.rfl, rfl, fun _ _ h => by subst h; rfl⟩



set_option maxRecDepth 100000 in
theorem record_heq {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hB : HEq Y.Bsup Y'.Bsup) (hd : HEq X.delta X'.delta) {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') :
    (∀ j b (x : Y.Fm i j b) (x' : Y'.Fm i' j b), HEq x x' → (x ∈ Y.Bsup i j b ↔ x' ∈ Y'.Bsup i' j b) ∧
      (∀ g g', HEq g g' → HEq (Y.actG i j b g x) (Y'.actG i' j b g' x')) ∧
      ∀ k P P', HEq P P' → HEq (Y.hkF i j b k P x) (Y'.hkF i' j b k P' x')) ∧
    (∀ (ε : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ε' : ∀ i, Bool → (FractionRing (X'.O i) →+* ℂ)), HEq ε ε' →
      ∀ b a a', HEq a a' → ε i b a = ε' i' b a') ∧
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → (P ∈ X.S0 i ↔ P' ∈ X'.S0 i') ∧
      ∀ σ' : Formalism.ConjugateSelfDual.G D'.host.E N'.Om, IsFrob (F := D'.host.E) (N'.plOm.1 P') (normV P') σ' →
        ∃ σ : Formalism.ConjugateSelfDual.G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ ∧ ∀ b : Bool,
          HEq (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i)
              ((if b then X.delta i σ else (X.delta i σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i)))
            (algebraMap (X'.O i') (FractionRing (X'.O i')) (algebraMap (X'.O0 i') (X'.O i')
              ((if b then X'.delta i' σ' else (X'.delta i' σ')⁻¹ : (X'.O0 i')ˣ) : X'.O0 i'))) := by
  obtain ⟨a1, a2, -, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  have xTw := h2.Tw
  have fixedFieldTransport_baseIntegerRing_heq := h2.O0
  have fixedFieldTransport_baseIntegerCommRing_heq := h2.crO0
  have xO := h2.O
  have xcrO := h2.crO
  have xalgO := h2.algO
  have fixedFieldTransport_initialPlaceSet_heq := h2.S0
  have yFm := h3.Fm
  have yacgFm := h3.acgFm
  have ymodFmK := h3.modFmK
  have ymodFmO := h3.modFmO
  have yactG := h3.actG
  have yhkF := h3.hkF
  clear h2 h3
  cases D; cases D'
  dsimp only at a1 a2
  subst a1; subst a2
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO fixedFieldTransport_initialPlaceSet_heq hd
  subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst fixedFieldTransport_initialPlaceSet_heq; subst hd
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yhkF hB
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yhkF; subst hB
  subst hi
  refine ⟨fun j b x x' hx => ?_, fun ε ε' hε b a a' ha => ?_, fun P P' hP => ?_⟩
  · subst hx
    exact ⟨Iff.rfl, fun g g' h => by subst h; rfl, fun k P P' h => by subst h; rfl⟩
  · subst hε; subst ha; rfl
  · subst hP
    exact ⟨Iff.rfl, fun σ hσ => ⟨σ, hσ, fun _ => HEq.rfl⟩⟩

section Ext

variable {LL LL' Ks Ks' WL WL' G G' : Type} [Field LL] [Field LL'] [NumberField LL']
  [Field Ks] [NumberField Ks] [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL']
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [IsScalarTower Ks LL WL]
  [AddCommGroup WL'] [Module LL' WL'] [Module Ks' WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  [IsScalarTower Ks' LL' WL']
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
  [Group G] [Group G']
  {ι : LL →+* LL'} {eK : Ks ≃+* Ks'} {γ : G ≃* G'} {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL' Ks' WL' W' G'}

end Ext

end GlobalTheory.TwInputs.Move.Forms

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.UnivCharCopy

theorem ring_relation_transfer_identity {R R' : Formalism.BasicNotions.Ranks} {H : Formalism.BasicNotions.Host R} {H' : Formalism.BasicNotions.Host R'} {Ω Ω' : Type}
    [iΩ : Field Ω] [iΩ' : Field Ω'] [aΩ : Algebra H.E Ω] [aΩ' : Algebra H'.E Ω'] {T T' : Type}
    {cc : Ω ≃+* Ω} {cc' : Ω' ≃+* Ω'} {l : T → ℕ} {l' : T' → ℕ}
    {d : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E Ω →* Multiplicative (DelQM H (l i) Q M)}
    {d' : ∀ i (Q : Finset (PlE H')) (M : ℕ), G H'.E Ω' →* Multiplicative (DelQM H' (l' i) Q M)}
    (hR : R = R') (hH : HEq H H') (hΩ : Ω = Ω') (hi : HEq iΩ iΩ') (ha : HEq aΩ aΩ') (hcc : HEq cc cc')
    (hT : T = T') (hl : HEq l l') (hd : HEq d d')
    (h : ∀ i Q M, d i Q M = GlobalTheory.GalChar.delU H cc (l i) Q M) :
    ∀ i Q M, d' i Q M = GlobalTheory.GalChar.delU H' cc' (l' i) Q M := by
  subst hR; cases hH; subst hΩ; cases hi; cases ha; cases hcc; subst hT; cases hl; cases hd
  exact h

theorem isUnivChar_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e), GlobalTheory.UnivChar.IsUnivChar D.nexp → GlobalTheory.UnivChar.IsUnivChar D'.nexp := by
  intro D D' ι e h hU
  exact ring_relation_transfer_identity h.gal.R h.gal.host (eq_of_heq h.gal.Om) h.gal.instOm h.gal.algOm h.set.cc
    (eq_of_heq h.set.Tw) h.set.l h.delU hU

end GlobalTheory.UnivCharCopy

end
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section
namespace GlobalTheory.RSCellEul

open GlobalTheory.RSnmEul GlobalTheory.RSnmUnf

theorem term_le_locFac {m k : ℕ} (h : m + 1 ≤ k) (q : ℕ) (a : Fin k → ℂ) (x : ℝ) (v : Fin (m + 1) → ℤ) :
    (if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≤
      GlobalTheory.RSCell.locFac q a x (padInt h v) := by
  split_ifs with hv
  · have hv' := padInt_valid h hv
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hv'.2, hv'.1⟩, toNat_padInt h v, sum_padNat h]
  · exact bot_le

theorem term_zero {m k : ℕ} (q : ℕ) (a : Fin k → ℂ) (x : ℝ) :
    (if (∀ i, 0 ≤ (0 : Fin (m + 1) → ℤ) i) ∧ Antitone (0 : Fin (m + 1) → ℤ) then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => ((0 : Fin (m + 1) → ℤ) i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, ((0 : Fin (m + 1) → ℤ) i).toNat : ℕ) : ℝ) * x))) else 0) = 1 := by
  have h0 : (fun i : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) i).toNat) = 0 := funext fun _ => rfl
  rw [if_pos ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩, h0, padNat_zero]
  rw [show (0 : Fin k → ℕ) = fun _ => 0 from rfl, GlobalTheory.RSPole.EulerPole.schurAt_const_zero]
  simp

theorem tprod_le_of_one_le {I : Type} (f g : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏' i, f i ≤ ∏' i, g i := by
  have hg : ∀ i, 1 ≤ g i := fun i => (hf i).trans (hfg i)
  rw [(GlobalTheory.RSPole.EulerPole.hasProd_of_one_le f hf).tprod_eq, (GlobalTheory.RSPole.EulerPole.hasProd_of_one_le g hg).tprod_eq]
  exact iSup_mono fun s => Finset.prod_le_prod' fun i _ => hfg i

theorem tsum_padTerm_ne_top : ∀ (E : Type) [Field E] [NumberField E] (m k : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), m + 1 ≤ k →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin k → ℂ) (x : ℝ),
    GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => α w.1 i) x ≠ ⊤ →
    ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≠ ⊤ := by
  intro E _ _ m k S hmk α x hfin
  classical
  let g : HeightOneSpectrum (𝓞 E) → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun w v =>
    if (∀ i, 0 ≤ v i) ∧ Antitone v then
      ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
        (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0
  show ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g ≠ ⊤
  have hg0 : ∀ w, g w 0 = 1 := fun w => term_zero _ _ _
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun i v => g i.1 v
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g = ∑' l' : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l'.prod f := by
    rw [← e.tsum_eq]; exact tsum_congr fun l => (he ℝ≥0∞ g hg0 l).symm
  rw [h1, (GlobalTheory.EulerSum.euler_product_intVec_ennreal (m + 1) f fun i => hg0 i.1).2]
  refine ne_top_of_le_ne_top hfin ?_
  rw [GlobalTheory.RSPole.eulD]
  refine tprod_le_of_one_le _ _ (fun i => ?_) (fun i => ?_)
  · exact le_of_eq_of_le (hg0 i.1).symm (ENNReal.le_tsum (f := f i) 0)
  · rw [GlobalTheory.RSCellSum.schurDir_eq_tsum_locFac]
    calc ∑' v, f i v ≤ ∑' v, GlobalTheory.RSCell.locFac (Ideal.absNorm i.1.asIdeal) (α i.1) x (padInt hmk v) :=
          ENNReal.tsum_le_tsum fun v => term_le_locFac hmk _ _ _ v
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (padInt_injective hmk) _

end GlobalTheory.RSCellEul
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

theorem _root_.GlobalTheory.T.thetaFunction_localGeneration_splitPlaceOffLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)), v ∈ Sb → (∃ ε e, IsPlaceIdem D v ε ∧ IsSplitIdem D e ∧ e * algebraMap (AF D.host.F) (AE D) ε ≠ 0) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ¬ GlobalTheory.DownLift.GenFinite.Over PP v) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.DownLift.GenFinite.TypeIn R i t Sb f → GlobalTheory.DownLift.GenFinite.CleanIn R i t Sb f → GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f → f ∈ Submodule.span ℂ (GlobalTheory.DownLift.GenFinite.StepGen R i t (GlobalTheory.DownLift.GenFinite.dropPl Sb v)) := by
  first | exact @GlobalTheory.DownLift.SplitGen.gen_split | exact GlobalTheory.DownLift.SplitGen.gen_split | (intros; apply GlobalTheory.DownLift.SplitGen.gen_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

theorem _root_.GlobalTheory.T.thetaShapeRelation_drop_splitPlace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), IsStdChar D R.ψ (-1) → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F) (a : AE D), IsSplitIdem D a → IsPlaceIdem D v ε → a + cA D a = algebraMap (AF D.host.F) (AE D) ε → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) → ∀ Φ f : WO (Vc D i) (Wc D i) → ℂ, HasShape R.ψ (Vc D i) (Wc D i) a Φ (R.vP i t) → HasShape R.ψ (Vc D i) (Wc D i) a Φ f → LikeOff R i t Sb f → LikeOff R i t (dropPl Sb v) f := by
  first | exact @GlobalTheory.DownLift.SplitRel.likeOff_dropPl | exact GlobalTheory.DownLift.SplitRel.likeOff_dropPl | (intros; apply GlobalTheory.DownLift.SplitRel.likeOff_dropPl <;> assumption)
end
