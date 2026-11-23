module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle780
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle798
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle799
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle739
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle267
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle091
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle016

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty
theorem latInt_member_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → ∀ big L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → (∀ i, (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i)) ∧ ∀ j h1 h2 w, (withLoc L).what₂.muAt w ≠ (withLoc L).what₂.mu0 → LatInt (withLoc L) (mtL L M) (C.Q w) j h1 h2 w := by
  intro D cf jE A M C tup hM big L hB
  obtain ⟨Sp, -, -⟩ := hB
  refine ⟨fun i => ?_, fun j h1 h2 w hw => ?_⟩
  · have h : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i h).trans (Sp.Qc_eq _ _)
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have h2' : j < D.R.m := h2
    exact ⟨(hM.full w ⟨j, h2'⟩ hw).1, fun v k s ϖ hg hc hu => hM.int w ⟨j, h2'⟩ v k s ϖ hw hg hc hu⟩
end GlobalTheory.CoefDuty
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty.MemberO
variable {D : D7}
end GlobalTheory.CoefDuty.MemberO
namespace GlobalTheory.CoefDuty.MemberO

theorem contains_fixZ_alt {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D} {C : NChoice D}
    {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ} {L : LocAll (lay0 D)}
    (hL : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) (i : L.X.nd.Loc) :
    Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) := by
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hL
  intro z hz
  obtain ⟨x, hx⟩ := Sp.iq_big i z hz
  refine ⟨x, ?_⟩
  change L.Y.naut.iotaQC i (L.Y.naut.iotaQ i x) = z
  rw [Au.iotaQ, Au.iotaQC]
  exact hx

theorem contains_big_of_built {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : MtFam D}
    {C : NChoice D} {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E} {big : D.what₂.places.Pl → Finset ℂ}
    {L : LocAll (lay0 D)} (hL : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L) (i : L.X.nd.Loc) :
    Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) :=
  _root_.GlobalTheory.CoefDuty.MemberO.contains_fixZ_alt hL i
theorem member_duties_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → ∀ i : L.X.nd.Loc, Contains (withLoc L).nd (withLoc L).naut i ↑(big (L.X.nd.w i)) ∧ Contains L.lay.fixZ.nd L.lay.fixZ.naut i ↑(big (L.X.nd.w i)) ∧ (Live (withLoc L).nd i ↔ Live L.lay.fixZ.nd i) ∧ (ZDecomp (withLoc L).nd i ↔ ZDecomp L.lay.fixZ.nd i) ∧ (∀ S, Chosen (withLoc L).nd (withLoc L).naut i S ↔ Chosen L.lay.fixZ.nd L.lay.fixZ.naut i S) ∧ ((∃ r, GoodR (withLoc L).nd i r) ↔ ∃ r, GoodR L.lay.fixZ.nd i r) ∧ ((∃ r ρ, GoodR (withLoc L).nd i r ∧ TakenWild (withLoc L).nd i r ρ) ↔ ∃ r ρ, GoodR L.lay.fixZ.nd i r ∧ TakenWild L.lay.fixZ.nd i r ρ) := fun _ _ _ _ _ _ _ _ L hL i =>
  ⟨_root_.GlobalTheory.CoefDuty.MemberO.contains_big_of_built hL i, _root_.GlobalTheory.CoefDuty.MemberO.contains_fixZ_alt hL i, live_iff L i, zdecomp_iff L i, chosen_iff L i, goodR_iff L i, taken_iff L i⟩
end GlobalTheory.CoefDuty.MemberO
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigPlace

theorem built_finite_and_mem_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB i x
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  exact finite_and_mem hstd (D := withLoc L) Hk.hecke Hk.av Hk.cover i x (C.Q (L.X.nd.w i)) hQ
end GlobalTheory.EigPlace
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigOnto


theorem main_alt_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L → ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w), ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, ∀ (v : PlE D.host) (k : ℕ), GenAt D (D.what₂.places.resChar w) (C.Q w) v k → iotaO L.X.nd L.Y.naut i ((L.X.nd.hT i v k : L.X.nd.X i → L.X.nd.O i) x) = c v k := by
  intro hstdP D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB j w h1 h2 hw c hc
  classical
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨-, y, hy, hcy⟩ := hc
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  have hb := Sp.B.iV_basis j w b
  obtain ⟨a⟩ : Nonempty (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hy
    have hy' : y ∈ Submodule.span ℂ (Set.range fun a => D.what₂.jMt (D.what₂.muTw w) j (b a)) := by
      rw [hjb.2]; exact Submodule.mem_top
    rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hy'
    exact hy'
  haveI : Nontrivial (Sp.B.V j w) := ⟨⟨Sp.B.iV j w (b a), 0, hb.1.ne_zero a⟩⟩
  obtain ⟨I0, hI0⟩ := Ideal.exists_maximal (heckeAlg Sp.B j w)
  obtain ⟨i0, hi0, -⟩ := Sp.mx_all j w h1 h2 hw I0 hI0
  have hinjC : Function.Injective (Sp.iotaC j w) := by
    intro a1 a2 hab
    obtain ⟨a1', rfl⟩ := (Sp.phO j w i0 hi0).surjective a1
    obtain ⟨a2', rfl⟩ := (Sp.phO j w i0 hi0).surjective a2
    rw [← Sp.iotaC_coh, ← Sp.iotaC_coh] at hab
    congr 1
    exact IsFractionRing.injective _ _ ((Sp.iq i0).injective ((qCast _ _).injective hab))
  let φ : FractionRing (Sp.B.Oc j w) →+* ℂ := IsFractionRing.lift hinjC
  have hφalg : ∀ z, φ (algebraMap _ _ z) = Sp.iotaC j w z := fun z => IsFractionRing.lift_algebraMap hinjC z
  have hφK : φ.comp (Sp.phK j w i0 hi0).toRingHom =
      (qCast (L.X.nd.w_l i0) (A.pl.ι (L.X.nd.w i0))).toRingHom.comp (Sp.iq i0) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (L.X.nd.O i0))
    ext z
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Sp.phK_alg, hφalg]
    exact (Sp.iotaC_coh j w i0 hi0 z).symm
  have hφ : ∀ x, φ (Sp.B.ec j w x) = D.what₂.embLL x := by
    intro x
    rw [← Sp.phK_emb j w i0 hi0 x, ← Sp.iq_LL i0 x]
    exact congrArg (fun f : FractionRing (L.X.nd.O i0) →+* ℂ => f (L.X.nd.embK i0 x)) hφK
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  obtain ⟨ej, ew⟩ := (L.X.nd.locs_mem j w i0).1 hi0
  have hμ0 : L.X.nd.mu i0 = D.what₂.muTw w := by rw [L.X.nd.mu_w i0, ew]
  have hQk : Hk.cover.B.Qc j w = C.Q w :=
    (Hk.cover.Q_eq j w i0 hi0).symm.trans ((Sp.Q_eq j w i0 hi0).trans (Sp.Qc_eq j w))
  have lin : ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → (M (D.what₂.muTw w) j h1 h2).wt.W),
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k (z • f + f') =
          z • NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f + NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k f' := by
    intro v k s ϖ hvk hc hu
    have H := GlobalTheory.LiftPoint.tN_lin (withLoc L) (mtL L M) Hk.hecke Hk.cover (j := j) (w := w) (i := i0) hi0 v k s ϖ
      (by rw [hQk]; exact hvk) hc hu
    exact GlobalTheory.FitHecke.mt_transport M (fun μ jj m => ∀ (z : ℂ) (f f' : GAf D.host.E D.R.nV → m.wt.W),
        NG.tN m.J s ϖ k (z • f + f') = z • NG.tN m.J s ϖ k f + NG.tN m.J s ϖ k f') hμ0 ej
      (L.X.nd.j_range i0).1 (L.X.nd.j_range i0).2 h1 h2 H
  have hstd : HeckeStdTw Sp.B := heckeStdTw_of_std Sp.std
  have hLoc : LocPl D j w := Or.inl hw
  have hgen : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      GenAt D (D.what₂.places.resChar w) (C.Q w) v k := fun v k h => by rw [← Sp.Qc_eq j w]; exact h
  have key : ∀ v k, GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k →
      ∃ κ : Sp.B.Oc j w, φ (algebraMap _ _ κ) = c v k := by
    intro v k hvk
    obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
    obtain ⟨tC, htC1, htC2⟩ := GlobalTheory.LiftPoint.tC_exists D M Sp.B hstd j w (D.what₂.muTw w) rfl h1 h2 hLoc φ hφ v k hvk
    have ht0 : tC y = c v k • y := by
      apply (M (D.what₂.muTw w) j h1 h2).real_inj
      rw [← htC2 s ϖ hc hu (lin v k s ϖ (hgen v k hvk) hc hu) y, hcy v k s ϖ (hgen v k hvk) hc hu, map_smul]
    exact htC1 (c v k) y hy ht0
  let κF : PlE D.host → ℕ → Sp.B.Oc j w := fun v k =>
    if hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k then Classical.choose (key v k hvk) else 0
  have hκF : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k), φ (algebraMap _ _ (κF v k)) = c v k := by
    intro v k hvk
    simp only [κF, dif_pos hvk]
    exact Classical.choose_spec (key v k hvk)
  obtain ⟨e, hene, he⟩ := GlobalTheory.PtLocalEig.eig_descends D M Sp.B j w (D.what₂.muTw w) h1 h2 rfl φ hφ
    (fun v k => algebraMap _ _ (κF v k)) y hy (by
      intro v k hvk
      obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
      refine ⟨s, ϖ, hc, hu, lin v k s ϖ (hgen v k hvk) hc hu, ?_⟩
      rw [hcy v k s ϖ (hgen v k hvk) hc hu, hκF v k hvk])
  have hinjK : Function.Injective (algebraMap (Sp.B.Oc j w) (FractionRing (Sp.B.Oc j w))) :=
    IsFractionRing.injective _ _
  obtain ⟨ψ, hψ, hψW⟩ := GlobalTheory.PtLocalEig.pt_of_eigvec (heckeGens Sp.B j w) e hene hinjK (by
    rintro _ ⟨v, k, hvk, rfl⟩
    exact ⟨κF v k, he v k hvk⟩)
  have hψv : ∀ v k (hvk : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k),
      ψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ = κF v k := by
    intro v k hvk
    apply hinjK
    have e1 := hψ ⟨Sp.B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩
    have e2 := he v k hvk
    change Sp.B.hK j w v k e = _ at e1
    rw [e2] at e1
    exact (smul_left_injective _ hene e1).symm
  have hW : NCov.W (heckeAlg Sp.B j w) (NCov.pt ψ) ≠ ⊥ := by
    intro h0
    apply hene
    have h3 := hψW
    rw [h0] at h3
    exact (Submodule.mem_bot _).1 h3
  obtain ⟨i, hi, hmx⟩ := Sp.mx_all j w h1 h2 hw (NCov.cls ψ) (NCov.cls_isMaximal ψ)
  refine ⟨i, hi, (Sp.ptX j w i hi).symm ⟨ψ, hmx.symm, hW⟩, fun v k hvk => ?_⟩
  have hvk' : GenAt D (D.what₂.places.resChar w) (Sp.B.Qc j w) v k := by rw [Sp.Qc_eq j w]; exact hvk
  have e1 : ∀ z, iotaO L.X.nd L.Y.naut i z = Sp.iotaC j w (Sp.phO j w i hi z) := by
    intro z
    unfold iotaO
    rw [RingHom.comp_apply, RingHom.comp_apply, Au.iotaQ i, Au.iotaQC i]
    exact Sp.iotaC_coh j w i hi z
  rw [e1, Sp.ptX_hT j w i hi _ v k hvk', Equiv.apply_symm_apply]
  show Sp.iotaC j w (ψ ⟨Sp.B.hK j w v k, _⟩) = c v k
  rw [hψv v k hvk', ← hφalg, hκF v k hvk']
end GlobalTheory.EigOnto
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TupleCharAtType
theorem xi_unrAt_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) :
    (P.tp.xi (D.nd.mu i)).UnrAt (D.naut.plGw k v) := by
  have hwg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hgp := D.host.g_prime k
  rw [D.nd.mu_w i, P.tp.xi_tw, D.nd.w_l i]
  have hdel : (P.cf.delAt (D.nd.l i)).UnrAt (D.naut.plGw k v) := by
    unfold CharFrame.delAt
    split_ifs
    · exact P.cf.isDel'.unr _ (natCast_notMem hgp D.host.pde'_prime (D.host.pde_ne_g k).2.symm hwg)
    · exact P.cf.isDel.unr _ (natCast_notMem hgp D.host.pde_prime (D.host.pde_ne_g k).1.symm hwg)
  have hpsi : (P.tp.psi (D.nd.w i)).UnrAt (D.naut.plGw k v) := by
    have hψ := P.tp.psi_is (D.nd.w i) (D.nd.w_tw i)
    by_cases hl : D.nd.l i = D.host.g k
    · intro x _
      refine hψ.atl _ ?_ x
      unfold OverP
      rw [D.nd.w_l i, hl]
      exact hwg
    · refine (hψ.ram _).2 ?_
      rw [← P.Q_eq i]
      have hlp : (D.nd.l i).Prime := (D.nd.lPrime i).out
      have hS : D.naut.plGw k v ∈ D.nd.S i := by
        rw [D.nd.S_def i]
        refine ⟨?_, natCast_notMem hgp hlp (Ne.symm hl) hwg⟩
        fin_cases k
        · exact Or.inl hwg
        · exact Or.inr (Or.inl hwg)
      exact Finset.disjoint_left.mp (D.nd.SQ_disj i) hS
  intro x hx
  change (P.cf.delAt (D.nd.l i)).loc _ x * (P.tp.psi (D.nd.w i)).loc _ x = 1
  rw [hdel x hx, hpsi x hx, one_mul]
theorem mu_unit_value_eq_loc_k_mu0 : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), u ∉ (D.naut.plGw k v).asIdeal → (((S i _ hw).mu (Units.map (algebraMap D.host.E ((D.naut.plGw k v).adicCompletion D.host.E)).toMonoidHom (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = (((P.cf.mu0 j).locK (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hL D P S hS i k v hw j hj u hu hnot
  rw [(hS.mu i _ hw j hj).2 (Units.mk0 (u : D.host.E) hu)]
  have hx := _root_.GlobalTheory.TupleCharAtType.xi_unrAt_alt P i k v _ (isUnitAt_of_notMem u hu hnot)
  show (((P.cf.mu0 j * P.tp.xi (D.nd.mu i)).loc (D.naut.plGw k v) (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  change (((P.cf.mu0 j).loc _ (atFin _ (Units.mk0 (u : D.host.E) hu)) *
    (P.tp.xi (D.nd.mu i)).loc _ (atFin _ (Units.mk0 (u : D.host.E) hu)) : ℂˣ) : ℂ) = _
  rw [hx, mul_one]
  rfl
end GlobalTheory.TupleCharAtType
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PtLocalPin

theorem eig_at_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q : D.naut.AV i)
    (w : PlE D.host) (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hcw : IsConjPl D.host w s.w)
    (hu : IsUnif D.host.E s.v ϖ) :
    ∃ c : ℕ → ℂ, X ^ D.R.nV + ∑ k ∈ Finset.Icc 1 D.R.nV,
        C ((-1 : ℂ) ^ k * ((normV w : ℕ) : ℂ) ^ (k * (k - 1) / 2) * c k) * X ^ (D.R.nV - k) =
      galPol D.naut (D.naut.lpTw (D.naut.locV i Q w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
      ∀ k, 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ D.naut.typeV i Q,
        NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) = c k • (P.M.loc i).real y := by
  classical
  have HT := P.H.hecke
  have hsB : s.v ∉ badPl D i := GlobalTheory.HeckeScalarAll.not_bad HT i hw s hcw
  have hex : ∀ k, ∃ c : ℂ, ∀ f ∈ P.H.av.S i Q,
      (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ → NG.rt D.host.E D.R.nV κ f = f) →
      NG.tN (Umax D.host.E D.R.nV) s ϖ k f = c • f := fun k =>
    GlobalTheory.T.splitPlace_heckeOperator_scalar_on_spherical D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s ϖ k hu
  choose c hc using hex
  have hfT : ∀ y, (P.M.loc i).real y ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    intro y
    rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
  have hfI : ∀ y ∈ D.naut.typeV i Q, (P.M.loc i).real y ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro y hy
    rw [P.H.av.typeV] at hy; exact hy
  have hfix : ∀ y, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real y) = (P.M.loc i).real y := by
    intro y κ hκ ht
    have ht' : TrivOutside (badPl D i)ᶜ κ :=
      GlobalTheory.HeckeScalarAll.trivOutside_mono (Set.singleton_subset_iff.2 hsB) ht
    obtain ⟨h1, h2⟩ := HT.J_hyp i κ ht'
    have hJ : κ ∈ (P.M.loc i).J := h1.2 hκ
    have e := (hfT y).2 ⟨κ, hJ⟩
    rw [h2 hJ] at e
    simpa using e
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨y0, hy0, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    have hf0 : (P.M.loc i).real y0 ≠ 0 := fun h =>
      hy00 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
    obtain ⟨g, hg, hg0, hgfix⟩ := exists_fixed_of_isoTyp (P.H.av.irr i Q) s.v _ (hfI y0 hy0) hf0 (hfix y0)
    have hpol := P.H.au.locPol (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) s w ϖ hcw hu
      (Umax D.host.E D.R.nV) (fun κ _ => Iff.rfl) g hg hg0 hgfix c (fun k _ _ => hc k g hg hgfix)
    rw [hpol, D.nbc.embAV_loc, P.H.emb]
  · intro k _ _ y hy
    have hfinU := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (Umax D.host.E D.R.nV) 1 ∅
      (fun κ _ => ⟨Iff.rfl, fun _ => rfl⟩) s ϖ k (by simp) hu
    have e1 : NG.tN (P.M.loc i).J s ϖ k ((P.M.loc i).real y) =
        NG.tN (Umax D.host.E D.R.nV) s ϖ k ((P.M.loc i).real y) := by
      simp only [NG.tN]
      rw [GlobalTheory.HeckeScalarAll.heckeD_eq_of_fixed (P.M.loc i).J (P.M.loc i).χ (badPl D i) (HT.J_hyp i) s hsB ϖ k _
        (hfix y)]
    rw [e1]
    exact GlobalTheory.HeckeScalarAll.tN_isoTyp (P.H.av.irr i Q) s ϖ k hfinU (c k) (hc k) _ (hfI y hy) (hfix y)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i,
    GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  intro hL D P i
  refine GlobalTheory.T.pointLocalEigen_galoisPolynomial_split D P.M P.H.hecke P.H.rational P.H.av P.H.cover i ?_
  intro Q w hw
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  obtain ⟨c0, hp0, -⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s0 ϖ0 hc0 hu0
  have hN : normV w ≠ 0 := (lt_trans zero_lt_one (GlobalTheory.WeilDeligne.one_lt_normV w)).ne'
  refine ⟨c0, hp0.symm, fun k s ϖ hc hu h1 h2 y hy => ?_⟩
  obtain ⟨c, hp, hy'⟩ := _root_.GlobalTheory.PtLocalPin.eig_at_alt P i Q w hw s ϖ hc hu
  rw [hy' k h1 h2 y hy, coeff_eq hN (hp.trans hp0.symm) h1 h2]

end GlobalTheory.PtLocalPin


theorem _root_.GlobalTheory.T.ptLocal_theta_exhaustion : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i := by
  exact _root_.GlobalTheory.PtLocalPin.main_alt_alt
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.IsoComp
open GlobalTheory.CompRed
section Gen
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {W : Type} [AddCommGroup W] [Module ℂ W]
end Gen
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (x : D.nd.X i) (f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)), f' ∈ eigC D.nd D.naut i x → f' ≠ 0 → ∀ sp : SplitPlace D.host.E, ∀ c : ℕ → ℂ, (∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real f') = c k • (P.M.loc i).real f') → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ ∃ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ F ≠ 0 ∧ ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) F = c k • F := by
  intro hL D P i x f' hf' hf0 sp c hc
  classical
  have hfin : ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k, ((fun y : GAf D.host.E D.R.nV =>
      (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J)) '' Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k).Finite := by
    intro ϖ hϖ k
    obtain ⟨N, hN, hNJ⟩ := (P.M.loc i).J_open
    exact GlobalTheory.T.finite_image_heckeSet_split_place_cosets D.host.E D.R.nV (P.M.loc i).J ⟨N, hN, fun κ hκ => (hNJ κ hκ).1⟩ sp ϖ k hϖ
  unfold eigC at hf'
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hf'
  obtain ⟨g, hgmem, hgsum⟩ := hf'
  have hg' : ∀ Q, g Q ≠ 0 → D.naut.ptV i Q = some x ∧ g Q ∈ D.naut.typeV i Q := by
    intro Q hQ
    by_cases h : D.naut.ptV i Q = some x
    · refine ⟨h, ?_⟩
      have := hgmem Q
      rwa [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from h)] at this
    · exfalso
      have := hgmem Q
      rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from h), Submodule.mem_bot] at this
      exact hQ this
  obtain ⟨Q0, hQ0⟩ : ∃ Q, g Q ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf0
    rw [← hgsum, show g = 0 from Finsupp.ext h, Finsupp.sum_zero_index]
  set G : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) := fun Q => (P.M.loc i).real (g Q) with hGdef
  have hsum : (P.M.loc i).real f' = ∑ Q ∈ g.support, G Q := by

    rw [← hgsum, Finsupp.sum, map_sum]
  have hGiso : ∀ Q ∈ g.support, G Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    intro Q hQ
    have hy := (hg' Q (Finsupp.mem_support_iff.1 hQ)).2
    rw [P.H.av.typeV] at hy
    exact hy
  have hind := isoTyp_indep (P.M.loc i).wt (P.H.av.S i) (P.H.av.irr i) (P.H.av.inj i)
  have hQ0s : Q0 ∈ g.support := Finsupp.mem_support_iff.2 hQ0
  refine ⟨Q0, (hg' Q0 hQ0).1, G Q0, hGiso Q0 hQ0s, ?_, ?_, ?_⟩
  · rw [← (P.M.loc i).real_range]
    exact ⟨g Q0, rfl⟩
  · intro h
    exact hQ0 ((P.M.loc i).real_inj (h.trans (map_zero (P.M.loc i).real).symm))
  · intro ϖ hϖ k hk
    set Dk := Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k
    set t : D.naut.AV i → (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
      fun Q => NG.heckeD (P.M.loc i).J Dk (G Q) - c k • G Q with htdef
    have htmem : ∀ Q ∈ g.support, t Q ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun Q hQ =>
      Submodule.sub_mem _ (heckeD_mem_isoTyp _ _ _ (hfin ϖ hϖ k) _ (hGiso Q hQ))
        (Submodule.smul_mem _ _ (hGiso Q hQ))
    have htsum : ∑ Q ∈ g.support, t Q = 0 := by
      simp only [t]
      rw [Finset.sum_sub_distrib, ← heckeD_finset_sum _ _ (hfin ϖ hϖ k), ← Finset.smul_sum, ← hsum, hc ϖ hϖ k hk,
        sub_self]
    have hrest : t Q0 = -∑ Q ∈ g.support.erase Q0, t Q := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase _ _ hQ0s, htsum]
    have hmem2 : t Q0 ∈ ⨆ (j : D.naut.AV i) (_ : j ≠ Q0), NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j) := by
      rw [hrest]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun Q hQ => ?_)
      obtain ⟨hne, hQs⟩ := Finset.mem_erase.1 hQ
      exact (le_iSup₂ (f := fun (j : D.naut.AV i) (_ : j ≠ Q0) => NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i j)) Q hne)
        (htmem Q hQs)
    have h0 : t Q0 = 0 := Submodule.disjoint_def.1 (iSupIndep_def.1 hind Q0) _ (htmem Q0 hQ0s) hmem2
    exact sub_eq_zero.1 h0
end GlobalTheory.IsoComp
end
end
end
