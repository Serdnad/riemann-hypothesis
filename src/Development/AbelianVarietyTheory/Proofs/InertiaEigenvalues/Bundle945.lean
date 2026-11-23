module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle104
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle086
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle118
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import GroundTheory.AutomorphicForms.Bundle012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolic
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle942
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle311
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle893
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverUnif



theorem exists_unf_dict : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (d : DeltaDat (T.Q.Xo j) c' 0) (σ₂ : d.c₂.F →+* ℂ),
    d.IsLev → d.l₂.A = 1 → σ₂.comp ((d.eF : c'.F →+* d.c₂.F).comp (incF T.Q.c c' hle)) = σ →
    ∃ (U₂ : Unf d.Xo₂ d.c₂ σ₂ D.R.r) (dict₂ : GA D (T.V j σ) → Σ k, Frame (U₂.X k).Ψ D.R.r),
      ∀ cc₂, (⟨c', hle, d, σ₂, U₂, dict₂, cc₂⟩ : Cover T j σ).IsUnif := by
  intro D T hT j hj σ hσ c' hle d σ₂ hlev hA hinc
  obtain ⟨hr, -⟩ := hT.modelW j hj σ hσ
  obtain ⟨hio, hx₀⟩ := GlobalTheory.TupleCover.iotaOK_and_frame T hT j hj σ hσ _ rfl hr
  have hpq := (exists_iotaOK D T.Q hT.pins j hj).2
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  have hg₂ : GoodEmb d.c₂ σ₂ := by
    have h1 := hσ
    rw [← hinc] at h1
    exact h1
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ σ₂ (T.V j σ) D.R.r hr _ hio hpos hA
    hg₂).2.2 (T.x₀ j σ) hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D (T.V j σ) d.l₂.M).1
  obtain ⟨un, dict, mu, hdict, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1
    ⟨continuous_const, fun _ => rfl⟩ (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, -, hdl⟩ := hP.dictLaws
  have hdom := (dict_invariant D _ _ _ _ _ _ _ _ C hC dict hdict Kf hKf).2.2.1
  refine ⟨C.unf un, dict, fun cc₂ => ⟨hlev, hA, hinc, hP.unf, hdom, hr, g, e, F, ik, φ, th, hP.modelW, hth, ?_⟩⟩
  rw [← hCι, ← hCx]
  exact hdl

end GlobalTheory.CoverUnif
end

section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧ ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ), φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)), ∀ 𝓕 𝓕₀ : Set (GA E (m + 1)),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤ → ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) 𝓕₀ μ ∧
      ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) h ∂μ =
        (c : ℂ) * ∫ h in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x h ∂μ := by
  first | (exact @GlobalTheory.RSnmUnfold.rs_unfold) | (exact GlobalTheory.RSnmUnfold.rs_unfold) | (intros; apply GlobalTheory.RSnmUnfold.rs_unfold  <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.equivariant_bilinearForms_vanish_of_io_generation_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (ι : Type) (B : ι → PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ), (∀ (j : ι) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → ∀ l, B j P' l = B j P (l ∘ₗ (R.cV i).ρ u)) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → (∀ j, B j P = 0) → ∀ j, B j P' = 0) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W) (j : ι), B j (R.ioP i x w) = 0) → ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (j : ι), B j P = 0 := by
  exact @GlobalTheory.GenByIo.forms_vanish_of_io
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)


attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlacesGood

variable {D : D7}

theorem over_pde_of_mem_pD (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h : P ∈ (D.ntw.pD i : Set (Pl D.host.E)) := hP
  rw [D.ntw.pD_eq i] at h
  split_ifs at h
  · exact ⟨_, Or.inr rfl, h⟩
  · exact ⟨_, Or.inl rfl, h⟩

theorem natCast_mem_of_conj {P P' : Pl D.host.E} (h : IsConjPl D.host P P') {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal :=
  (h (n : 𝓞 D.host.E) (n : 𝓞 D.host.E) (by simp)).1 hn

theorem splitsC_of_primesOver {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
  have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
  rw [h] at e
  exact e

theorem coprime_of_level {p : ℕ} (hp : p.Prime) (hs : p ∉ D.host.small) (hq : p ≠ D.host.q) (hl : p ∈ D.host.levelPrimes) :
    Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p :=
  Nat.Coprime.mul_left (UpperTheory.Ram.coprime_QSq D.host hp hs hq)
    (D.host.ccK_coprime p (by simp [hl]))

theorem count_AA_eq_zero {P : Pl D.host.E} {p : ℕ} (hc : Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p)
    (hp : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : FractionalIdeal.count D.host.E P D.host.AA = 0 :=
  GlobalTheory.HalfCompare.primeToAA_of_not_mem (GlobalTheory.HalfCompare.not_mem_of_coprime P hc hp)

theorem placesOK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL hsp hq i ch hch
  classical
  have hPg : ∀ P ∈ Rl.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Rl.C.P.Div k P := fun P hP => by
    obtain ⟨k, hk⟩ := (hL.Pg P).1 hP
    exact ⟨k, GlobalTheory.Mem.TypePl.div_over Rl.C.P hk, hk⟩
  have hQ : ∀ P ∈ half ch (D.ntw.pD i), ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => over_pde_of_mem_pD i (mem_half.1 hP).1
  have hsm : ∀ p : ℕ, p.Prime → GlobalTheory.Mem.Chr.SplitsC D.host.E p → p ∉ D.host.small := fun p hp h hs =>
    UpperTheory.Ram.not_dvd_condN_of_unram D.host hp (fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p hp h w hw).2.1)
      (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  have hpp : ∀ p, (p = D.host.pde ∨ p = D.host.pde') → p.Prime ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E p ∧
      Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p ∧ ∀ k, p ≠ D.host.g k := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, splitsC_of_primesOver D.host.pde_prime hsp.1,
        coprime_of_level D.host.pde_prime (hsm _ D.host.pde_prime (splitsC_of_primesOver D.host.pde_prime hsp.1)) hq.1 D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1⟩
    · exact ⟨D.host.pde'_prime, splitsC_of_primesOver D.host.pde'_prime hsp.2,
        coprime_of_level D.host.pde'_prime (hsm _ D.host.pde'_prime (splitsC_of_primesOver D.host.pde'_prime hsp.2)) hq.2 D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2⟩
  refine ⟨⟨Rl.Pg ∪ half ch (D.ntw.pD i), Finset.subset_union_left, Finset.subset_union_right, ?_⟩, ?_, ?_⟩
  · refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => ?_) fun P hP P' hP' hc => ?_
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨k, hk, -⟩ := hPg P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
    · rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨k, hk, hd⟩ := hPg P hP
        obtain ⟨k', hk', hd'⟩ := hPg P' hP'
        have e := GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (D.host.g_prime k) (D.host.g_prime k') (natCast_mem_of_conj hc hk) hk'
        have hkk : k = k' := by
          have := D.host.g_ne
          fin_cases k <;> fin_cases k' <;> simp_all
        subst hkk
        exact GlobalTheory.Mem.TypePl.not_isConjPl Rl.C.P (D.nd.g_split k) hd hd' hc
      · obtain ⟨k, hk, -⟩ := hPg P hP
        obtain ⟨p, hp, hm⟩ := hQ P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) hm (natCast_mem_of_conj hc hk))
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        obtain ⟨k, hk, -⟩ := hPg P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) (natCast_mem_of_conj hc hm) hk)
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        have hs := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
        exact (hch.pair P P' hc (ne_of_split hs hc)).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    obtain ⟨k, hk, -⟩ := hPg P hP
    obtain ⟨p, hp, hm⟩ := hQ P hP'
    exact (hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P (hpp p hp).1 (D.host.g_prime k) hm hk)
  · intro PP hPP PP' hPP'
    have hmem : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := fun n hn => by
      rcases hPP' with rfl | hc
      · exact hn
      · exact GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc hn
    rcases hPP with hPP | hPP
    · obtain ⟨k, hk, -⟩ := hPg PP hPP
      exact count_AA_eq_zero (GlobalTheory.CoverHalf.g_coprime D k).symm (hmem _ hk)
    · obtain ⟨p, hp, hm⟩ := hQ PP hPP
      exact count_AA_eq_zero (hpp p hp).2.2.1 (hmem _ hm)

end GlobalTheory.SeriesTie.PlacesGood

end
end
