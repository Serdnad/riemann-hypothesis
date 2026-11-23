module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle112
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle060
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle105
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitHecke
section NC
open Formalism.L2.NCov Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] {S : Set (End K V)}
end NC
section Conj
variable {R : Ranks}
end Conj
section Gen
variable {D : D7} {M : MtFam D}
end Gen
section Chars
open Formalism.L2.Host
end Chars


theorem heckeOpen_withLoc_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), ∃ Hk : _root_.GlobalTheory.HeightCounting.HeckeOpenStatements (withLoc L) (mtL L M) tp.tup, ∀ j h1 h2 π, Hk.au.cls j h1 h2 π = A.au.cls j h1 h2 π := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hjf : ∀ i : L.X.Loc, L.X.j i - 1 + 1 = L.X.j i := fun i => by have := L.X.j_range i; omega
  let jf : L.X.Loc → Fin D.R.m := fun i => ⟨L.X.j i - 1, by have := L.X.j_range i; omega⟩
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStd cover.B := Sp.std
  refine ⟨{ hecke := ?_, av := { S := Au.S, irr := Au.irr, inj := Au.inj, surj := Au.surj, typeV := Au.typeV, ptV := Au.ptV }, au := { A.au with }, emb := Au.emb, rational := rational_of cover, level := ?_, data := { bj := Sp.bj, bj_span := Sp.bj_span, bj_rel := fun i c => Sp.bj_rel i (sOf _ i) (sOf_spec _ i) c }, cover := cover }, fun j h1 h2 π => rfl⟩
  · refine { J_hyp := fun i => ?_
             hT := hT_of cover hstd Sp.act_hK
             sameO := sameO_of cover
             sep := sep_of cover hstd
             Q_conj := Q_conj_of cover
             Q_same := Q_same_of cover fun j j' w => (Sp.Qc_eq j w).trans (Sp.Qc_eq j' w).symm }
    have h0 := hMt.hyp (L.X.w i) (jf i)
    have h1 := hypOutside_transport' (M := M) (L.X.mu_w i).symm (hjf i) _ _ (L.X.j_range i).1 (L.X.j_range i).2 _ h0
    refine hypOutside_mono (D := withLoc L) _ _ ?_ h1
    have hi := mem_locs_self (D := withLoc L) i
    have hQe : C.Q (L.X.w i) = L.X.Q i := ((Sp.Q_eq _ _ i hi).trans (Sp.Qc_eq _ _)).symm
    intro v hv
    rcases hv with hv | hv
    · exact gPl_sub_badPl (D := withLoc L) i hv
    · obtain ⟨w', hov, hw'⟩ := qPl_sub tp (L.X.w i) (L.X.w_tw i) (jf i) hv
      refine ⟨w', hov, ?_⟩
      rcases hw' with hQ | hp
      · left
        rw [hQe] at hQ
        exact hQ
      · right; right
        rw [L.X.w_l i] at hp
        exact hp
  · refine { prod := ?_, para := ?_, uni := ?_, wt := ?_, hyp := ?_ }
    · exact fun i => mt_transport M (fun μ j m => NG.IsProdLevel m.J) (L.X.mu_w i).symm (hjf i) _ _ _ _
        (hMt.prod (L.X.w i) (jf i))
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ v ∈ qPl D (tp.tup μ j),
        ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.para (L.X.w i) j)
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
        s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.uni (L.X.w i) j)
    · intro μ j t sh a lam hinf hdual hhw
      have e := infG_etaT A.chr t
      have hsh : sh = 1 / 2 := by
        have := Multiset.singleton_inj.1 (hinf.symm.trans e)
        rw [this]; push_cast; ring
      rw [hsh]
      exact hMt.wt μ j t a lam hdual hhw
    · exact fun i j hj => mt_transport M (fun μ jj m => NG.HypOutside m.J m.χ (gPl D ∪ qPl D (tp.tup μ j)))
        (L.X.mu_w i).symm hj _ _ _ _ (hMt.hyp (L.X.w i) j)
end GlobalTheory.FitHecke
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.LocLevel


theorem level_at_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  intro D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr
  classical
  have hov : NG.OverPl w s.v := overPl_of_isConjPl hc
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hS := (X.nd.S_def i w).not.1 hw.2.2.1
  have hl := hw.2.1
  have hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl' hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hw.2.2.2 hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl' hov hov' hp')
  have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
    intro v hv
    apply htr v
    rintro rfl
    exact hv hvB
  exact hyp κ htr'
end GlobalTheory.LocLevel
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR


theorem rhoS_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (hcheb : GlobalTheory.RowTie.ChebSplit b.D.nd) (hP : RowPar (withLoc b.L)) (hG : GalRepEx (withLoc b.L))
    (hC : ClassFieldHeckeAlgebraic (withLoc b.L)) (hη : EtaShiftInt (withLoc b.L)) (a : (withLoc b.L).nd.Loc)
    (s : (withLoc b.L).ntw.Sig ((withLoc b.L).ntw.twOf a))
    (hs : (withLoc b.L).ntw.side _ s = (withLoc b.L).ntw.twSide a) (hj : (withLoc b.L).ntw.jS _ s = (withLoc b.L).nd.j a) :
    ∃ (σ : (withLoc b.L).what₂.FT) (hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) σ ≠ ⊥)
      (hg : (withLoc b.L).nd.goodRow σ),
      ∀ (π : (withLoc b.L).naut.CG (withLoc b.L).R.r) (hS : rowSig (withLoc b.L) a σ = [⟨(withLoc b.L).R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
            ((withLoc b.L).ntw.rhoS _ s))
          (rhoOfRow (withLoc b.L) hG hC hη a π (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).1
            (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).2) := by
  obtain ⟨hiso, hgood, hspec⟩ := b.Bs.rhoS (b.L.T.twOf a) s
  have hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) (b.Bs.rowS (b.L.T.twOf a) s) ≠ ⊥ := by
    rw [← hj]; exact hiso
  refine ⟨b.Bs.rowS (b.L.T.twOf a) s, hσ, hgood, fun π hS => ?_⟩
  obtain ⟨hc, hr⟩ := rowSig_csd_ralg (withLoc b.L) hP a _ hσ hgood π hS
  have hloc : ∀ w, IsSplitPl b.D.host w → b.D.naut.locG π w = b.A.row.locR (b.Bs.rowS (b.L.T.twOf a) s) w := by
    intro w hw
    have h1 := (rowSig_spec (withLoc b.L) hP a _ hσ).2.2 w hw
    rw [hS] at h1
    exact ((isoLoc_single (withLoc b.L) π w).symm.trans h1).trans (b.Au.locW a _ w)
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  let φ0 : FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) →+* Qbar ((withLoc b.L).nd.l a) :=
    ((withLoc b.L).naut.iotaQ a).comp (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))
  have hφ0 : φ0.comp (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)))) =
      (Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a) := by
    ext y
    show (withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y)) =
      (withLoc b.L).naut.iotaQ a (algebraMap _ _ ((withLoc b.L).ntw.twist₂ a y))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
  have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
      ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
      (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
    fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
      (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
  let φ := (castQ hpq).symm.toRingHom.comp φ0
  let ι := (castQ hpq).trans ((withLoc b.L).naut.iotaQC a)
  have hφ : ∀ z : ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)], φ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)) =
      algebraMap ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] (Qbar ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))) (z : ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)]) := by
    intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  have hι : ∀ x : ↥b.D.LL0, ι (φ ((if (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a)
      else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x)) = embLL0 b.D x := by
    intro x
    have hs' : (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s = (withLoc b.L).ntw.twSide a := hs
    rw [hs']
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  have hR := hspec π hc hr hloc φ ι hφ hι
  have hR' : IsRepOf (withLoc b.L) ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)) ((castQ hpq).trans ((withLoc b.L).naut.iotaQC a))
      ((withLoc b.L).naut.tw π (withLoc b.L).naut.etaTinv) ((1 - ((withLoc b.L).R.nV : ℝ)) / 2)
      (Formalism.MainNotions.N.mapRep (castQ hpq).symm.toRingHom (Formalism.MainNotions.N.mapRep
        ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
        ((withLoc b.L).ntw.rhoS _ s))) := by
    rw [← hφ0, mapRep_mapRep]
    exact hR
  exact conj_of_isRepOf (withLoc b.L) ((withLoc b.L).naut.iotaQC a) _ _ hcheb _ _
    (isRepOf_cast (withLoc b.L) hpq _ _ _ _ hR') (rhoOfRow_isRepOf (withLoc b.L) hG hC hη a π _ _)
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting


theorem nRhoTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → TypesOpen (withLoc b.L) b.jE → NR.NRhoTied (withLoc b.L) := by
  intro hL D' b _ _ _ hcheb hT
  exact ⟨hT.rbarSS, hT.rbar, fun hP hG hC hη a s hs hj =>
    _root_.GlobalTheory.HeightCounting.FitRho.rhoS_withLoc_alt hL D' b hcheb hP hG hC hη a s hs hj⟩
end GlobalTheory.HeightCounting
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.joint_conditions_range_bound_alt : GlobalTheory.Published.FontaineBcris → Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D) (X : KillingConditions.HubData D), _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt large₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → GlobalTheory.SplitCoef.OSplit D → GlobalTheory.PtCore.PtFam D X.r X.ρ → (∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i) → (∀ i, AbsIrreducibleDistinct D i (X.r i)) ∧ (∀ i, KillingConditions.RangeAD large₂ X.exc (D.nd.l i) → ∀ π, ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i (X.r i) π M0 h0 (X.cB i)) ∧ (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.ambDual (D := D) i (X.ρ i) π (X.dc i)) ∧ (∀ i π, EmbeddingTypes.H1fFiniteRankTorsion (D := D) i (X.ρ i) π (X.dc i)) := by
  exact _root_.GlobalTheory.closingFamilyX_alt_alt
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
noncomputable section
namespace GlobalTheory.LocCoincide


theorem built_laws_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D →
    GlobalTheory.RowTie.CharLaws D.nd D.naut ∧
    (∀ (i i' : D.nd.Loc) (σ : D.what₂.FT) (v : PlE D.host), IsSplitPl D.host v → D.naut.locW i σ v = D.naut.locW i' σ v) ∧
    (∀ i i' : D.nd.Loc, D.nd.j i = D.nd.j i' → D.nd.w i = D.nd.w i' → D.naut.muC i = D.naut.muC i') := by
  intro hL D b
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩ := b
  subst eq
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.RowLaws.main _ _ _ _ _ A.wdT).2.1
  · intro i i' σ v _
    exact (Au.locW i σ v).trans (Au.locW i' σ v).symm
  · intro i i' hj hw
    have hj' : L.X.nd.j i = L.X.nd.j i' := hj
    have hw' : L.X.nd.w i = L.X.nd.w i' := hw
    have hjr : 1 ≤ L.X.nd.j i ∧ L.X.nd.j i ≤ D0.R.m := L.X.nd.j_range i
    have hmu : L.X.nd.mu i = L.X.nd.mu i' :=
      (L.X.nd.mu_w i).trans ((congrArg _ hw').trans (L.X.nd.mu_w i').symm)
    have e1 : L.X.nd.j i - 1 + 1 = L.X.nd.j i := by omega
    have e2 : L.X.nd.j i - 1 + 1 = L.X.nd.j i' := by omega
    have h1 := Au.muC i ⟨L.X.nd.j i - 1, by omega⟩ e1
    have h2 := Au.muC i' ⟨L.X.nd.j i - 1, by omega⟩ e2
    show L.Y.muC i = L.Y.muC i'
    apply A.chr.e1.injective
    apply Subtype.ext
    exact h1.trans ((congrArg (fun μ => tp.tup μ ⟨L.X.nd.j i - 1, by omega⟩) hmu).trans h2.symm)
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (M : Formalism.L2.MtFam D), _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D →
    Formalism.L2.HeckeTied D M → KillingConditions.LocalisationUniqueness D := fun hL D M b hT =>
  have h := _root_.GlobalTheory.LocCoincide.built_laws_alt hL D b
  GlobalTheory.T.localization_eq_of_heckeAgreement_twistLaws D M hT h.1 h.2.1 h.2.2
end GlobalTheory.LocCoincide
end
end
end
