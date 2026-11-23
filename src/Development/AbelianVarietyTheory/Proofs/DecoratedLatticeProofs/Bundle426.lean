module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle089
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle349
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle345
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle171
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle283
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle297
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle353
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle379
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.LocMod

theorem flatFB_holds : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  intro D hFL hFLs hOm k _ _ _ _ _ _ p ν hν ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm
  have hstd : IsStdChar D ψ (-1) := st.weil.std
  obtain ⟨hcont, hne⟩ := (GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hstd).2.1 ψk hχ
  have hc : c = 2 * σ + 1 := hBF.1
  let L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO J.W₀ B.V₀ → ℂ) :=
    { toFun := fun Φ => flatFB st (Tm Φ)
      map_add' := fun Φ Φ' => by
        simp only [map_add (f := _)]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ')).1
      map_smul' := fun a Φ => by
        simp only [map_smul, RingHom.id_apply]
        exact (GlobalTheory.T.jacobiToBesselFlatSchwartz_add_smul D hFL ψ hstd σ J B st _ _ (hTm.theta Φ) (hTm.theta Φ)).2 a }
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.flatMap_laws_factor_fourierJacobi_source k ψk ν hcont hne hν n n' c σ (WO J.W₀ B.V₀ → ℂ) L hc
    (GlobalTheory.T.flat_fourierJacobi_to_bessel_column_mul_laws D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_row_multiplication D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.localFlatMap_translationLaws_jacobiToBessel_free D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
    (GlobalTheory.T.fourierJacobi_bessel_flatMap_unipotent_law D hFLs hOm k p ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm)
  exact ⟨L₀, GlobalTheory.T.fourierJacobi_bessel_flatMap_factor_isLocalModel D hFLs hOm k p ν hν ψ ψk hχ σ J B st s hs n n' c G₀ FW FA F₀ FV hJF hCF hBF Tm hTm L₀ hL₀, hL₀⟩

end GlobalTheory.LocMod

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedLat

theorem movedLat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P := by
  intro D L hT Gi Gl Kc Yd cX ex W _ j hj g
  obtain ⟨c, hc⟩ := W.Q.charW.base.lev.βY j hj
  have hsd : IsSelfDualC (Yc D j) ((pk W).ΛY j) := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩
  exact (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D (Yc D j) _ hsd).1 g

end GlobalTheory.MovedLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelPlaces

theorem not_isConjPl_lev {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : ¬ Formalism.BasicNotions.IsConjPl D.host P P) :
    ¬ Formalism.IndefR.Lev.IsConjPl (D := D) P P := by
  intro hl
  apply h
  intro x y hxy
  have hs : ∀ c c' : 𝓞 D.host.E, (c' : D.host.E) = star (c : D.host.E) → c' = GlobalTheory.IdemSupport.cO D c :=
    fun c c' e => RingOfIntegers.ext (by rw [e, GlobalTheory.IdemSupport.cO_coe])
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  subst hy
  constructor
  · intro hx
    obtain ⟨c', hc', e⟩ := hl x hx
    rwa [hs _ _ e] at hc'
  · intro hx
    obtain ⟨c', hc', e⟩ := hl _ hx
    rwa [hs _ _ e, GlobalTheory.IdemSupport.cO_cO] at hc'

end GlobalTheory.LevelPlaces

namespace GlobalTheory.LevelPlaces

theorem split_unit : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg → ∀ PP ∈ (pk W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) = GlobalTheory.FinPl.latV V Λ (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hpk hTy PP hPP
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hTy.1 PP hPP
  rw [Nat.cast_mul] at hg
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hgp : (D.host.g k).Prime := D.host.g_prime k

  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rw [map_natCast]; exact hk

  obtain ⟨i, hi⟩ := ((GlobalTheory.PlacesOverG.places_over_g_k D k).2.1 PP).1 hk
  have key : ∀ {v v' : HeightOneSpectrum (𝓞 D.host.F)}, v = v' → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v') := by
    rintro v _ rfl h; exact h
  have hτ : Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
    rcases i with w | w
    · have hi' : D.naut.plGw k w = PP := hi
      exact key (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi')
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
    · have hi' : GlobalTheory.IdemSupport.cP (D.naut.plGw k w) = PP := hi
      exact key ((GlobalTheory.IdemSupport.under_cP _).symm.trans (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi'))
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
  obtain ⟨τ⟩ := hτ
  have he := GlobalTheory.AdelicU.Supp.splitAt_splitIdemAd (D := D) τ
  have hε := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
  have hs := he.2.2.trans (GlobalTheory.AdelicU.Supp.pl_eq D ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)))
  have hsplit : IsSplitIdem D (GlobalTheory.AdelicU.Supp.splitIdemAd _ τ) := ⟨he.1, he.2.1, _, _, hε, hs⟩
  obtain ⟨p, -, hpv⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D _ _ _ hsplit hε hs

  have hne : ∀ m ∈ D.host.condN.primeFactors, D.host.g k ≠ m := fun m hm e => by
    have := GlobalTheory.RamValCheck.g_coprime D k m hm
    rw [e, Nat.coprime_self] at this
    exact hgp.one_lt.ne' (e ▸ this)
  have hc : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hgp).2 fun ⟨m, hm⟩ => ?_)
    refine hpk.aa PP (Or.inr (Or.inl hPP)) ?_
    rw [hm, Nat.cast_mul]
    exact PP.asIdeal.mul_mem_right _ hk
  have hu := GlobalTheory.FinPl.UnitAt.unitAA_of_prime p hgp (by rw [hpv]; exact hv) (UpperTheory.Ram.g_notMem_small D k)
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.q_prime, D.host.q_dvd_condN, D.host.condN_ne_zero⟩))
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.d_prime, D.host.d_dvd_condN, D.host.condN_ne_zero⟩)) hc
  unfold GlobalTheory.FinPl.SplitPt.UnitAA at hu
  rw [hpv] at hu
  exact ⟨⟨_, _, hsplit, hε, hs⟩, hu.1, hu.2⟩

end GlobalTheory.LevelPlaces
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd
open GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

abbrev lineZ (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem gram_X' {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) : (I.rec7 l Z).sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by
    rintro _ n rfl; exact gram_pos hs n
  exact key _ _ h2

def oTop {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) :
    ∀ n, n = (I.rec7 l Z).R.m → OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)) :=
  fun n h => Eq.rec (motive := fun n _ => OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)))
    (topDec (gram_X hI _) (gram_X' hI)) h.symm

def piE (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : (I.rec7 l Z).host.E :=
  ((X.piT u : 𝓞 B.host.E) : B.host.E)

def zeta (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : Fin (lineZ (I.rec7 l Z)).rank → (I.rec7 l Z).host.E :=
  fun _ => piE I l Z u

def xgeo {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok)
    (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (u : B.Word)
    (Λ : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : XGeo (I.rec7 l Z) :=
  ⟨fun _ => stdSp _, vac, lineZ _, oTop l Z hI, zeta I l Z u, 1, Λ⟩

theorem norm_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    star (zeta I l Z u) ⬝ᵥ (lineZ (I.rec7 l Z)).gram *ᵥ zeta I l Z u = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  have h := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (l.pr.piT_norm u)
  rw [gram_pos, Matrix.one_mulVec]
  simp only [dotProduct, zeta, piE, Pi.star_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_mul, map_natCast] at h
  rw [show (lineZ (I.rec7 l Z)).rank = 1 from rfl, one_smul]
  exact (mul_comm _ _).trans h

theorem isLineVec_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    IsLineVec (lineZ (I.rec7 l Z)) (zeta I l Z u) := by
  refine ⟨rfl, ?_⟩
  rw [norm_zeta]
  have := (l.pr.T_prime u).ne_zero
  exact_mod_cast this

theorem eq_latFrame_of_isSDFrame {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.PlaceModel.latFrame V := by
  obtain ⟨c, -, -, -, h4, h5⟩ := h
  ext x
  constructor
  · intro hx
    have := h5 x hx
    rw [one_pow, Nat.cast_one, one_smul] at this
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame]
    exact this
  · intro hx
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame] at hx
    have := h4 x hx
    rwa [one_pow, Nat.cast_one, one_smul] at this

end GlobalTheory.XGeoStd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Topology

noncomputable section

namespace GlobalTheory.WeilCondUnif

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (p : SplitPt D k) (hU : p.UnitAA) : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := pr_int p (hU.1 _ hm).2.2
  rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this

theorem hasConductor_of_mul {χ ψk : AddChar k Circle} {ξ : k} (hv : valuation k ξ = 1) (he : ∀ x, ψk x = χ (ξ * x))
    (h : HasConductor χ 1) : HasConductor ψk 1 := by
  intro x
  rw [← h x]
  have hξ0 : ξ ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  constructor
  · intro H y hy
    have := H (ξ⁻¹ * y) (by rw [map_mul, map_inv₀, hv, inv_one, one_mul]; exact hy)
    rwa [he, ← mul_assoc, mul_inv_cancel₀ hξ0, one_mul] at this
  · intro H y hy
    rw [he]
    exact H _ (by rw [map_mul, hv, one_mul]; exact hy)

theorem hasConductor_weil (q : SplitPt D k) (hU : q.UnitAA) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (ψk : AddChar k Circle) (h : (ofSplit q).IsChar ψ ψk) (hx : (ofSplit q).xi ≠ 0) : HasConductor ψk 1 := by
  have h' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := h
  set ξ : k := q.pr (incA D D.host.xi0) with hξ
  have hξ0 : ξ ≠ 0 := hx
  have hx0 : D.host.xi0 ≠ 0 := fun h0 => hξ0 (by rw [hξ, h0, map_zero, map_zero])
  have hinv : q.pr (incA D D.host.xi0⁻¹) = ξ⁻¹ := map_inv₀ (q.pr.comp (incA D)) D.host.xi0
  have h1 : valuation k ξ ≤ 1 := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral q hU)
  have h2 : valuation k ξ⁻¹ ≤ 1 := by rw [← hinv]; exact (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hv : valuation k ξ = 1 := by
    have hp : valuation k ξ * valuation k ξ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k ξ * valuation k ξ⁻¹ := hp.symm
      _ ≤ valuation k ξ * 1 := mul_le_mul_right h2 _
      _ = valuation k ξ := mul_one _
  have hχ : q.IsChar ψ (ψk.mulShift ξ⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, h', mul_comm ξ⁻¹ a, ← hinv, sec_mul_pr, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
      map_one, one_mul]
  refine hasConductor_of_mul hv (fun x => ?_) (hasConductor_one D k q ψ _ hψ hχ hU)
  rw [AddChar.mulShift_apply, ← mul_assoc, inv_mul_cancel₀ hξ0, one_mul]

theorem int_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (z : AE D) : q.pr z ∈ 𝒪[k] ↔ q'.pr z ∈ 𝒪[k'] := by
  rw [q.int_iff, q'.int_iff, q.sec_pr, q'.sec_pr, he]

theorem dense_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (hd : DenseRange (q'.pr.comp (incA D))) :
    DenseRange (q.pr.comp (incA D)) := by
  let f : k' → k := fun y => q.pr (q'.sec y)
  have hf : Continuous f := q.cont_pr.comp q'.cont_sec
  have hs : Function.Surjective f := fun a => ⟨q'.pr (q.sec a), by
    show q.pr (q'.sec (q'.pr (q.sec a))) = a
    rw [q'.sec_pr, ← he, e_mul_sec, q.pr_sec]⟩
  have hc : f ∘ (q'.pr.comp (incA D)) = q.pr.comp (incA D) := funext fun a => by
    show q.pr (q'.sec (q'.pr (incA D a))) = q.pr (incA D a)
    rw [q'.sec_pr, ← he, map_mul, pr_e, one_mul]
  have := hs.denseRange.comp hd hf
  rwa [hc] at this

end Local

section Unif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] [NumberField K]

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem isUnif_of (P : HeightOneSpectrum (𝓞 K)) (ι : K →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P a)
    (hd : DenseRange ι) (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 K) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ (ϖ : k) = ι ((Formalism.L2.Col.qOf P : ℕ) : K) := by
  have hvN := GlobalTheory.AtTypeExists.valuation_norm P hq
  set N : K := ((Formalism.L2.Col.qOf P : ℕ) : K) with hN
  have hN0 : N ≠ 0 := fun h0 => WithZero.exp_ne_zero (hvN.symm.trans (by rw [h0, map_zero]))
  have hI : ∀ a, valuation k (ι a) ≤ 1 ↔ P.valuation K a ≤ 1 := fun a => by
    rw [← GlobalTheory.AtTypeExists.intAt_iff, ← hint, Valuation.mem_integer_iff]
  have hvN1 : P.valuation K N ≠ 0 := by rw [hvN]; exact WithZero.exp_ne_zero
  have K1 : ∀ a : K, valuation k (ι a) < 1 → valuation k (ι a) ≤ valuation k (ι N) := by
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, map_zero, map_zero]; exact zero_le'
    have ha0 : valuation k (ι a) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact (map_ne_zero ι).2 a0
    have h1 : ¬ P.valuation K a⁻¹ ≤ 1 := by
      rw [← hI, map_inv₀, map_inv₀]
      intro h
      have := mul_le_mul_right h (valuation k (ι a))
      rw [mul_inv_cancel₀ ha0, mul_one] at this
      exact not_le.2 ha this
    have hPa : P.valuation K a < 1 :=
      lt_of_le_of_ne ((hI a).1 ha.le) (fun h => h1 (by rw [map_inv₀, h, inv_one]))
    have hle := lt_one_le_exp hPa
    have hdiv : P.valuation K (a / N) ≤ 1 := by
      calc P.valuation K (a / N) = P.valuation K a * (P.valuation K N)⁻¹ := by rw [map_div₀, div_eq_mul_inv]
        _ ≤ P.valuation K N * (P.valuation K N)⁻¹ := mul_le_mul_left (hle.trans_eq hvN.symm) _
        _ = 1 := mul_inv_cancel₀ hvN1
    have h2 := (hI _).2 hdiv
    calc valuation k (ι a) = valuation k (ι (a / N)) * valuation k (ι N) := by
          rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hN0]
      _ ≤ 1 * valuation k (ι N) := mul_le_mul_left h2 _
      _ = valuation k (ι N) := one_mul _
  have hexp : WithZero.exp (-1 : ℤ) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have K2 : valuation k (ι N) < 1 := by
    refine lt_of_le_of_ne ((hI N).2 (hvN.trans_le hexp)) fun h => ?_
    have h3 : valuation k (ι N⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, h, inv_one]
    rw [hI, map_inv₀, hvN, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    norm_num at h3
  refine ⟨Units.mk0 (ι N) ((map_ne_zero ι).2 hN0), fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx K2⟩, rfl⟩
  rw [Units.val_mk0]
  by_cases x0 : x = 0
  · rw [x0, map_zero]; exact zero_le'
  have hx0 : valuation k x ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact x0
  have hs : {y : k | valuation k (y - x) < valuation k x} ∈ 𝓝 x :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.1 (hd x) _ hs
  have e : valuation k (ι a) = valuation k x := Valuation.map_eq_of_sub_lt _ hy
  rw [← e] at hx ⊢
  exact K1 a hx

end Unif

theorem cond_unif : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a PP hPP l
  have hstd : IsStdChar D (pk W).ψ (-1) := W.Q.stdChar
  refine ⟨?_, GlobalTheory.SplitWeil.exists_isUnitVol l.k, fun hQ => ?_⟩
  · obtain ⟨⟨ψk, hψk⟩, -, hxi, -⟩ := GlobalTheory.LocChar.weil_char_split D l.k (ofSplit l.q) (pk W).ψ hstd
    exact ⟨ψk, hψk, hasConductor_weil l.q l.unit _ hstd ψk hψk hxi⟩
  · obtain ⟨t, ht⟩ := hQ
    obtain ⟨⟨p, -, hcard, hp2, -⟩, -⟩ := W.Q.charW.base.lev.Q_pl t PP ht
    have hqp : Formalism.L2.Col.qOf PP = p := by
      rw [← hcard]
      unfold Formalism.L2.Col.qOf
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hq2 : ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by rw [hqp]; exact hp2
    obtain ⟨k', _, _, _, _, q', hqe, -, hint', hd'⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP l.q.e l.idem
    have hint : ∀ x, (l.q.pr.comp (incA D)) x ∈ 𝒪[l.k] ↔ Formalism.L2.Col.IntAt PP x := fun x =>
      (int_transfer l.q q' hqe.symm (incA D x)).trans (hint' x)
    have hd := dense_transfer l.q q' hqe.symm hd'
    obtain ⟨ϖ, hu, hϖ⟩ := isUnif_of PP _ hint hd hq2
    exact ⟨ϖ, hu, ⟨hint, hd, rfl, hϖ⟩⟩

end GlobalTheory.WeilCondUnif
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]


end
end
