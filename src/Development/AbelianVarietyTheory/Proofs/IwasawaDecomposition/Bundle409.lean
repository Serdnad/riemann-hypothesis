module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle326
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle394
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC

noncomputable section

namespace GlobalTheory.HeckeLocN



section Transport

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂} {i : LocT B} {j : ℕ} {w : what₂.places.Pl}
  (h : jOf B i = j ∧ wOf B i = w)

def trO : OOf B i ≃+* B.Oc j w := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

def trK : FractionRing (OOf B i) ≃+* FractionRing (B.Oc j w) := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

theorem trK_alg (z : OOf B i) : trK h (algebraMap _ _ z) = algebraMap _ _ (trO h z) := by obtain ⟨rfl, rfl⟩ := h; rfl

theorem trK_ec (x : what₂.LL) : trK h (B.ec _ _ x) = B.ec j w x := by obtain ⟨rfl, rfl⟩ := h; rfl

variable (hC : PartCompl B) (hL : MtLoc B hC)

def trPsi : TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) →ₛₗ[(trK h).toRingHom] B.V j w := by
  obtain ⟨rfl, rfl⟩ := h
  exact { toFun := PsiC B hC hL i, map_add' := map_add _, map_smul' := fun c z => map_smul (PsiC B hC hL i) c z }

theorem trPsi_inj : Function.Injective (trPsi h hC hL) := by obtain ⟨rfl, rfl⟩ := h; exact PsiC_inj B hC hL i

theorem trPsi_range (y : B.V j w) : y ∈ NCov.part (heckeAlg0 B j w) (mxC B j w i) ↔ ∃ z, trPsi h hC hL z = y := by
  obtain ⟨rfl, rfl⟩ := h
  rw [mxC_self]
  exact PsiC_range B hC hL i y

theorem trPsi_pr (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) (x' : what₂.MtL (what₂.muTw w) j) (hx : HEq x' x) :
    trPsi h hC hL (prMtC B hC hL i x) - B.iV j w x' ∈ NCov.off (heckeAlg0 B j w) (mxC B j w i) := by
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := eq_of_heq hx
  rw [mxC_self]
  exact PsiC_pr B hC hL i _

def trX : XOf B i ≃ {ψ : heckeAlg0 B j w →ₐ[B.Oc j w] B.Oc j w //
    NCov.cls ψ = mxC B j w i ∧ NCov.W (heckeAlg0 B j w) (NCov.pt ψ) ≠ ⊥} := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun x => ⟨x.1, x.2.1.trans (mxC_self B i).symm, x.2.2⟩, fun x => ⟨x.1, x.2.1.trans (mxC_self B i), x.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem trX_hT (x : XOf B i) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) :
    trO h ((hTOf B i v k : XOf B i → OOf B i) x) = (trX h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact ptX_val B i v k hvk x

theorem trPsi_act (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd))
    (hA : ActHK B hs hd hL hAct) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) (z) :
    trPsi h _ hL (((actC B (partCompl_of hs hd) hAct i) (hTOf B i v k)).baseChange (FractionRing (OOf B i)) z) =
      B.hK j w v k (trPsi h _ hL z) := by
  obtain ⟨rfl, rfl⟩ := h
  exact hA i v k hvk z

include h in
theorem tr_max : (mxC B j w i).IsMaximal := by obtain ⟨rfl, rfl⟩ := h; exact mxC_max B i

end Transport

variable {D : D7}

def recBase (M : MtFam D) (B0 : LocBase0 D.host D.what₂)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w) : NLocBase D M where
  Oc := B0.Oc
  ec := B0.ec
  ec_w := B0.ec_w
  V := B0.V
  iV := B0.iV
  iV_basis := B0.iV_basis
  Qc _ w := B0.Qw w
  hL := B0.hL
  hL_def := hdef
  hK := B0.hK
  hK_def := B0.hK_def
  split := B0.split
  Qc_over _ := hO
  Qc_conj _ := hc

section Spec

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D) (hs : HeckeStd0 B0) (hd : FinDimV B0)
  (hL : MtLoc B0 (partCompl_of hs hd))
  (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hTL : ∀ i, IsLocalRing (TOf B0 i)) (hAct : ActEx B0 (partCompl_of hs hd))
  (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
  (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
  (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
  (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
  (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
  (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
  (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
  (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
  (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i))

attribute [local instance] LocBase0.algOc



theorem nonempty_spec
    (hTwE : ∀ (a : LocT B0) (x : D.LL0) (y : D.ntw.O0 (C.twI (wOf B0 a))),
      algebraMap (D.ntw.O0 (C.twI (wOf B0 a))) (FractionRing (D.ntw.O0 (C.twI (wOf B0 a)))) y =
        (if C.sd (wOf B0 a) then D.ntw.emb0 (C.twI (wOf B0 a)) else D.ntw.emb0b (C.twI (wOf B0 a))) x →
      B0.ec (jOf B0 a) (wOf B0 a) (x : D.what₂.LL) = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y))
    (hOrd : ∀ a g, ∃ n : ℕ, ps a g ^ (lOf B0 a ^ n) = 1)
    (hOpen : ∀ a, IsOpen ((ps a).ker : Set (G D.host.E D.nd.Om)))
    (hAnti : ∀ a, AntiHom D.ntw.cc (ps a))
    (hRamP : ∀ a, RamExactly (ps a) (↑(B0.Qw (wOf B0 a)) : Set (HeightOneSpectrum (𝓞 D.host.E))))
    (hPl : ∀ a v, v ∈ placesOver D.host.E (lOf B0 a) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Dec (F := D.host.E) A, ps a σ = 1)
    (pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w)
    (hQ : ∀ w, B0.Qw w = C.Q w)
    (iq : ∀ j w, FractionRing (B0.Oc j w) →+* Qbar (D.what₂.places.resChar w))
    (hiA : ∀ j w (z : ℤ_[D.what₂.places.resChar w]), iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))
      (algebraMap ℤ_[D.what₂.places.resChar w] (B0.Oc j w) z)) =
        algebraMap ℚ_[D.what₂.places.resChar w] (Qbar (D.what₂.places.resChar w)) (z : ℚ_[D.what₂.places.resChar w]))
    (hiL : ∀ j w x, pl.ι w (iq j w (B0.ec j w x)) = D.what₂.embLL x)
    (hBig : ∀ j w, ∀ z ∈ big w, ∃ x, pl.ι w (iq j w x) = z)
    (hAHK : ActHK B0 hs hd hL hAct) (hD : PlGwDisj D)
    (hψ : ∀ (a : LocT B0) (g : G D.host.E D.nd.Om) (y : D.what₂.LL), C.embW (wOf B0 a) y =
      algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
        (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
          ((C.psi' (wOf B0 a) (D.ntw.art (C.twI (wOf B0 a)) (C.Q (wOf B0 a)) g) :
            (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))ˣ) : D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))) →
      B0.ec _ _ y = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) ((ps a g : (OOf B0 a)ˣ) : OOf B0 a))
    (hTwA : ∀ a : LocT B0, haveI : Fact (D.ntw.l (C.twI (wOf B0 a))).Prime := D.ntw.lPrime (C.twI (wOf B0 a))
      ∀ (z : ℤ_[D.ntw.l (C.twI (wOf B0 a))]) (z' : ℤ_[D.what₂.places.resChar (wOf B0 a)]), HEq z z' →
      tw a (@algebraMap _ (D.ntw.O0 (C.twI (wOf B0 a))) _ _ (D.ntw.algO0 (C.twI (wOf B0 a))) z) = algebraMap _ (OOf B0 a) z')
    (hTwR : ∀ a : LocT B0, ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (OOf B0 a) →+* Ω)
      (ι : FractionRing (C.Oe (wOf B0 a)) →+* Ω),
      (∀ y, τ (algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y)) =
        ι (algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
          (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
            (BlochKatoReduction.Gen.phiK D.ntw (C.twI (wOf B0 a)) (C.k' (wOf B0 a)) y)))) ∧
      ∀ x : D.what₂.LL, τ (B0.ec _ _ x) = ι (C.embW (wOf B0 a) x))
    (hBr : ∀ j w (u : PlE D.host), u ∈ placesOver D.host.E (D.what₂.places.resChar w) →
      ∃ Bw : LocBridge (D.what₂.places.resChar w) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 u)) (B0.Oc j w),
        (∀ x, x ∈ D.nd.plOm.1 u ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef D.host.condN Bw.LL ∧
        ∀ z : B0.Oc j w, iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w)) z) =
          ((Bw.toLL z : ↥Bw.LL.1) : Loc.Om (D.what₂.places.resChar w))) :
    Nonempty (NdSpec pl M C big (mkX B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF) (mkT B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF hTwE hOrd hOpen hAnti hRamP hPl)) := ⟨{
  iq i := iq (jOf B0 i) (wOf B0 i)
  iq_alg i := hiA _ _
  iq_LL i := hiL _ _
  iq_big i := hBig _ _
  B := recBase M B0 hdef hO hc
  Q_eq j w i h := congrArg B0.Qw ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h).2
  mx := mxC B0
  mx_max j w i h := tr_max ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  mx_inj := mxC_inj B0 (locsFin_of hs hd)
  mx_all := mxC_all B0 (locsFin_of hs hd)
  phO j w i h := trO ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK j w i h := trK ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_alg j w i h := trK_alg ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_emb j w i h := trK_ec ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  Psi j w i h := trPsi ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_inj j w i h := trPsi_inj ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_range j w i h := trPsi_range ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_pr j w i h x := trPsi_pr ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL x _ (cast_heq _ _)
  ptX j w i h := trX ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  ptX_hT j w i h := trX_hT ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  iotaC j w := (pl.ι w).toRingHom.comp ((iq j w).comp (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))))
  iotaC_coh j w i h z := by
    obtain ⟨rfl, rfl⟩ := ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
    rfl
  Qc_eq _ := hQ
  std := hs
  act_hK j w i h := trPsi_act ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) hs hd hL hAct hAHK
  twOf_eq _ := rfl
  twSide_eq _ := rfl
  psi_eq := hψ
  twO_alg := hTwA
  tw_reads a := ⟨tw a, HEq.rfl, hTwR a⟩
  heckeLoc_gamma_places _ := gamN_tg D hD
  nbr i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose
  nbr_ind i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.1
  self_good i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.1
  nbr_iq i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.2
  bj := bjC B0 hI
  bj_span := bjC_span B0 hI
  bj_rel i s hs' c := by
    obtain rfl : s = sOfC B0 hI i := RingHom.ext fun y => IsFractionRing.injective (OOf B0 i) (FractionRing (OOf B0 i))
      ((hs' y).trans (congrArg Subtype.val ((fracRangeEquiv (OOf B0 i)).apply_symm_apply ⟨_, hI _ _ y⟩)).symm)
    exact bjC_rel B0 hI i c }⟩

end Spec

end GlobalTheory.HeckeLocN
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLiftN

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem unif_ne_zero {s : SplitPlace L} {ϖ : s.v.adicCompletion (maximalRealSubfield L)}
    (hϖ : IsUnif L s.v ϖ) : ϖ ≠ 0 := by
  rintro rfl
  have : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
  rw [map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem tSet_subset_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k ⊆ tSet L n s ϖ' k := by
  rintro x ⟨hx, a, ha, b, hb, e⟩
  have h0 := unif_ne_zero hϖ'
  have h0' := unif_ne_zero hϖ
  set u := ϖ / ϖ' with hu
  have hu0 : u ≠ 0 := div_ne_zero h0' h0
  have hv : Valued.v u = 1 := by
    rw [hu, map_div₀]
    have e1 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have e2 : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
    rw [e1, e2, div_self WithZero.exp_ne_zero]
  have hvi : Valued.v u⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
  let c : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u else 1
  let c' : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u⁻¹ else 1
  have hcc : (fun i => c i * c' i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  have hcc' : (fun i => c' i * c i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  let dm : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨Matrix.diagonal c, Matrix.diagonal c', by rw [Matrix.diagonal_mul_diagonal, hcc, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, hcc', Matrix.diagonal_one]⟩
  have hI : ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z ≤ 1 →
      z ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun z hz =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ s.v).2 hz
  have hdm : dm ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeStdFacts.mem_GLint_iff]
    refine ⟨fun i j => hI _ ?_, fun i j => hI _ ?_⟩
    · show Valued.v (Matrix.diagonal c i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c]; split_ifs
        · rw [hv]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
    · show Valued.v (Matrix.diagonal c' i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c']; split_ifs
        · rw [hvi]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
  have hdiag : Formalism.UG.diagJ n ϖ k = Formalism.UG.diagJ n ϖ' k * (dm : Matrix (Fin n) (Fin n) _) := by
    show _ = _ * Matrix.diagonal c
    rw [Formalism.UG.diagJ, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [c]
    split_ifs
    · rw [hu]; field_simp
    · rw [one_mul]
  refine ⟨hx, a, ha, dm * b, mul_mem hdm hb, ?_⟩
  rw [e, Units.val_mul, hdiag]
  simp only [Matrix.mul_assoc]

theorem tSet_eq_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k = tSet L n s ϖ' k :=
  Set.Subset.antisymm (tSet_subset_of_unif n s ϖ ϖ' k hϖ hϖ') (tSet_subset_of_unif n s ϖ' ϖ k hϖ' hϖ)

theorem tN_eq_of_conj (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf D.host.E n))
    (v : PlE D.host) (s s' : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (ϖ' : s'.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (hc : IsConjPl D.host v s.w)
    (hc' : IsConjPl D.host v s'.w) (hu : IsUnif D.host.E s.v ϖ) (hu' : IsUnif D.host.E s'.v ϖ') (f : GAf D.host.E n → W) :
    NG.tN J s ϖ k f = NG.tN J s' ϖ' k f := by
  have hw : s.w = s'.w := GlobalTheory.TwSys.ResidualCompare.isConjPl_unique hc hc'
  obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq _ s s' hw
  unfold NG.tN
  rw [tSet_eq_of_unif n s ϖ ϖ' k hu hu']

end GlobalTheory.HeckeLiftN

namespace GlobalTheory.HeckeLiftN

theorem heckeLift (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) :
    HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  intro hP hG hI j w v k h1 h2 hg
  classical
  by_cases hex : ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ
  swap
  · exact ⟨0, fun s ϖ hc hu _ => absurd ⟨s, ϖ, hc, hu⟩ hex⟩
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex
  obtain ⟨B, hB, hBs⟩ := hG w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj' : j' < D.R.m := by omega
  set Mw := M (D.what₂.muTw w) (j' + 1) h1 h2 with hMw
  have hrat : ∀ x, ∃ x', Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x') =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) :=
    fun x => hI.rat w ⟨j', hj'⟩ v k s0 ϖ0 hg hc0 hu0 x
  obtain ⟨-, Plin, -, -⟩ := hP D.host.E D.R.nV Mw.wt Mw.J Mw.χ B Mw.J_open hB s0 ϖ0 k (hBs v k s0 hg hc0) hu0
    hg.2.2.2.2.1 hg.2.2.2.2.2
  have hTS : ∀ y, Mw.real y ∈ NG.TypeSp Mw.wt.ρ Mw.J Mw.χ := fun y => by
    rw [← Mw.real_range]; exact LinearMap.mem_range_self _ y
  have hRJ : Function.Injective fun x => Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x) :=
    Mw.real_inj.comp (Formalism.L2.jMt_injective _ _)
  have htN0 : NG.tN Mw.J s0 ϖ0 k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
    have := Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    rw [one_smul, add_zero, one_smul] at this
    simpa using this
  let T0 : D.what₂.MtL (D.what₂.muTw w) (j' + 1) → D.what₂.MtL (D.what₂.muTw w) (j' + 1) := fun x => (hrat x).choose
  have hT0 : ∀ x, Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) := fun x => (hrat x).choose_spec
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := by
    intro x y
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (x + y))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x + T0 y))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y)) 1
    rw [one_smul, one_smul] at this
    rw [hT0, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hT0, hT0, this]
  have hsmul : ∀ (a : D.what₂.LL) x, T0 (a • x) = a • T0 x := by
    intro a x
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (a • x))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (a • T0 x))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) 0 (Submodule.zero_mem _) (D.what₂.embLL a)
    rw [add_zero, htN0, add_zero] at this
    rw [hT0]
    simp only [LinearMap.map_smulₛₗ, RingHom.id_apply]
    rw [hT0, this]
  let T : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) (j' + 1)) :=
    { toFun := T0
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨T, fun s ϖ hc hu x => ?_⟩
  show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
    NG.tN Mw.J s ϖ k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x))
  rw [hT0]
  exact tN_eq_of_conj D Mw.J v s0 s ϖ0 ϖ k hc0 hc hu0 hu _

end GlobalTheory.HeckeLiftN
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelColumnsGoodRows_le_principal_and_finiteDimensional : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → R.EEat (R.levR F true) ≤ R.EEat R.triv ∧ FiniteDimensional ℂ (MultR R F) := by
  first | exact @GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | exact GlobalTheory.Mem.SRe.levCols_le_triv_and_finite | (intros; apply GlobalTheory.Mem.SRe.levCols_le_triv_and_finite <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∀ (uE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, (Y.Ish.jE y).1 = PiTensorProduct.lift (R.HE.e (uE y))) → ∀ y, LinearMap.adjoint (R.Th A3.A.μ0) (uE y) ∈ Submodule.span ℂ (Set.range fun x => R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x))) := by
  first | exact @GlobalTheory.UpKeep3.adjoint_mem_span_rowForm | exact GlobalTheory.UpKeep3.adjoint_mem_span_rowForm | (intros; apply GlobalTheory.UpKeep3.adjoint_mem_span_rowForm <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  first | exact @GlobalTheory.EvalAllRows.evalTranslate_norm_all | exact GlobalTheory.EvalAllRows.evalTranslate_norm_all | (intros; apply GlobalTheory.EvalAllRows.evalTranslate_norm_all <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CuspRep.UnrSat

open GlobalTheory.CuspRep GlobalTheory.LFun GlobalTheory.PRep

theorem exists_hasSatGL_locRep : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (v : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.LGrp.IsSpherical (π.locRep v) (GlobalTheory.LFun.KGL v (n := a)) → ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL v (π.locRep v) B := by
  intro hF E _ _ _ a π v hs
  obtain ⟨σ, hσ, hadm⟩ := LocEx.exists_isLocComp hF E a π v
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨y, hy0, hy⟩ := LocSph.exists_fixed_of_mem_iSup ((finRep E a).comp (locGL E a v)) σ.ρ σ.irred
    (fun f : LocSph.Maps π v σ => f.1) (fun f => f.2.2) (KGL v (n := a) : Set _) x.1 (fun e => hx0 (Subtype.ext e))
    (fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hx k hk))
    (by rw [LocSph.iSup_range_eq π v σ hσ]; exact x.2)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (KGL v (n := a)) :=
    (Submodule.ne_bot_iff _).2 ⟨y, GlobalTheory.LGrp.mem_fixed.2 hy, hy0⟩
  have hfin : FiniteDimensional ℂ (fixed σ.ρ (KGL v (n := a))) :=
    hadm.2 _ (SatCompare.isOpen_isCompact_KGL v a).1 (SatCompare.isOpen_isCompact_KGL v a).2
  obtain ⟨B, hB⟩ := SatCompare.exists_hasSatGL ⟨σ.smooth, σ.irred⟩ hfin hsph
  exact ⟨B, HeightCounting.Blocks.hasSatGL_locRep hσ hB⟩

end GlobalTheory.CuspRep.UnrSat
end
end
