module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle176
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle426
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle117
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle231
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle151
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle088
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl

@[expose] public section

section



section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.CovTop.DegProof

theorem covering_degree_eq_alt : HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  intro hX h2 hS hT hG hQ hN hDG hSz hF
  have hP := _root_.GlobalTheory.T.covering_topology_refinement h2
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.valuation_multiplicity_run_estimate_alt h2 hG hQ hS hT hN hDG hSz hF) _root_.GlobalTheory.HSApp.wtBig_run_alt)
    (Closed.and (Closed.and (_root_.GlobalTheory.T.weight_parameter_strict_antitone_alt hSz) (_root_.GlobalTheory.T.size_bounds_for_family_alt hSz)) hDG)) ?_
  rintro eps Fm CH - ⟨⟨⟨_, -, a₁⟩, _, -, a₂⟩, ⟨⟨_, -, a₃⟩, _, -, a₄⟩, _, -, a₅⟩
  obtain ⟨x0, a⟩ := (a₁.and a₂).and ((a₃.and a₄).and a₅)
  clear a₁ a₂ a₃ a₄ a₅
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨a₁, a₂⟩, ⟨a₃, a₄⟩, a₅⟩ := a x hx hle ι p hp
  clear a
  obtain ⟨hp1, hq1, hE, hQuo, hAnti, -, -⟩ := a₃ i hi
  obtain ⟨hLaw, hIn, -⟩ := a₄ i hi Y hY
  obtain ⟨-, -, -, -, -, -, ⟨Z'⟩, -⟩ := a₅ i hi Y hY
  have hW := a₂ i hi
  have hV := a₁ i hi Y hY
  rw [hQuo u1 hu1]
  have hPr := _root_.GlobalTheory.T.proportionality_principle_compactification h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hEq := _root_.GlobalTheory.T.compactification_top_chern_eq_volume h2 hS hT hN _ p.T hLaw _ hp1 hq1 hE hIn Y _ _ hY.1
  have hBir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS hP h2.q15 h2.q16 _ p.T hLaw _ hp1 hq1 Y _ _ hY.1 _ (fun τ a b hab => by
    have hb := b.2
    have h := hW.gaps τ a (by rw [← hab]; exact hb)
    rw [gap_eq _ hab] at h
    refine le_trans ?_ h
    have e : ∀ d C N : ℕ, (d + 3) ^ 2 + 2 * N ≤ (d + 3) * (C + 4 * N + d + 3) := fun d C N => by nlinarith
    rw [GlobalTheory.CompHS.dimFlag_eq]
    exact_mod_cast e _ _ _)
  have key := GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.1.unf hPr.1 hEq _ (fun τ => (hAnti τ).1) (fun τ => (hAnti τ).2) hBir hV
  refine ⟨CompHt.delPrime Y.U Z' _, ?_, fun Z => key Z Z'⟩
  exact mul_pos (hPr.2 Z') (Int.cast_pos.2 (CompHt.vdm_pos fun τ => (hAnti τ).2))
end GlobalTheory.CovTop.DegProof
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.coverDegree_of_grothendieck_deformation : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree := by
  first | exact @_root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | exact _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt | (intros; apply _root_.GlobalTheory.CovTop.DegProof.covering_degree_eq_alt <;> assumption)
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


theorem GlobalTheory.AutPart.exists_autSpec_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq Y Cb) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp
  classical
  choose ι hfin F hF using fun i : X.nd.Loc => GlobalTheory.T.algebraicModularForms_irreducible_decomposition D (X.nd.mu i) (X.nd.j i) (mlX M X i)
  have irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (F i P) := fun i => (hF i).1
  have hinj := fun i => (hF i).2.1
  have hsurj := fun i => (hF i).2.2.1
  have hne := fun i => (hF i).2.2.2.1
  have hind := fun i => (hF i).2.2.2.2.1
  have htop := fun i => (hF i).2.2.2.2.2
  obtain ⟨ptV, hptV⟩ : ∃ ptV : ∀ i, ι i → Option (X.nd.X i), ∀ i P x, ptV i P = some x ↔
      (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) := by
    refine ⟨fun i P => if h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) then some h.choose else none, fun i P x => ?_⟩
    dsimp only
    by_cases h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)
    · rw [dite_eq_left h]
      constructor
      · rintro ⟨⟩; exact h.choose_spec
      · intro hx
        rw [_root_.GlobalTheory.T.galois_family_local_condition_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i _ (hne i P) _ _ h.choose_spec hx]
    · rw [dite_eq_right h]
      exact ⟨fun h' => absurd h' (by simp), fun hx => (h ⟨x, hx⟩).elim⟩
  have hpts := fun i => haveI := hfin i; _root_.GlobalTheory.T.galois_family_unramified_outside_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i)
  choose μ hμc hμ using _root_.GlobalTheory.T.galois_family_crystalline_weights_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose κ hκ using _root_.GlobalTheory.T.galois_family_determinant_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose b hb using fun i : X.nd.Loc => GlobalTheory.algWt_contragredient D.host.E D.R.nV (mlX M X i).wt
  have hralg : ∀ {a} (π : D.naut.CG a) τ, D.naut.ralg π → ∀ z ∈ D.naut.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
    fun π τ h => ((D.naut.ralg_def π).1 h τ).2
  refine ⟨{
    iotaQ := Sp.iq
    iotaQC := fun i => (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)))
    iota_LL := Sp.iq_LL
    iotaQ_alg := Sp.iq_alg
    muC := μ
    muC_csd := hμc
    AV := ι
    finAV := hfin
    ptV := ptV
    typeV := fun i P => ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real)
    typeV_ne := hne
    typeV_indep := hind
    typeV_top := htop
    pt_surj := fun i => (hpts i).1
    eig_dim := fun i => (hpts i).2
    locV := fun i P w => D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    satV := fun i P w => D.nbc.satAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    locV_unr := fun i P w => haveI := hfin i; _root_.GlobalTheory.T.galois_family_irreducible_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w
    pt_loc := fun i P x hx w hw => haveI := hfin i; _root_.GlobalTheory.T.galois_family_trace_frobenius_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i) P x hx w hw
    infWt := fun i => D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
    locW := fun i σ w => A.row.locR σ w
    satW := fun i σ w => A.row.satR σ w
    lab_loc := fun i k σ v => A.row.lab_eq k σ v
    wdOf := fun i {a} r w => A.wd.wdOf (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_dim := fun i {a} r w => A.wd.wdOf_dim (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_unr := fun i {a} r w => A.wd.wdOf_unr (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_frob := fun i {a} r w => A.wd.wdOf_frob (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_ine := fun i {a} r w => A.wd.wdOf_ine (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0 := fun i {a} r w => A.wd.wdOf_mono0 (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsCrysW := fun i {a} r w => A.wd.IsCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsPotCrysW := fun i {a} r w => A.wd.IsPotCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsdRW := fun i {a} r w => A.wd.IsdRW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsW := fun i {a} r τ => A.wd.jumpsW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r τ
    wdOf_unrL := fun i {a} r w => A.wd.wdOf_unrL (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0L := fun i {a} r w => A.wd.wdOf_mono0L (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsInf := fun i {a} π τ => (D.naut.infG π ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf a)
    locAutHodgeTateWeightsLevelZero := fun i τ => (D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
      ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf D.R.nV)
    jumpsInf_def := fun i {a} π τ h => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec a z (hralg π _ h z hz)
    locAut_hodgeTateWeightsLevelZero_def := fun i τ => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec _ z ((D.nbc.infW_alg _ _ _).2 z hz)
    chi_mu := fun i w hw => _root_.GlobalTheory.T.galois_family_hecke_compatible_alt hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i (μ i) (hμc i) (hμ i) w hw
    kFbar := κ }, {
    embAV := fun i P => (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P })
    embAV_inj := fun i P P' h => hinj i P P' ((A.au.iso _ _ _ _ _).1 h).2
    embAV_loc := fun _ _ _ => rfl
    embAV_sat := fun _ _ _ => rfl
    embAV_sph := fun i P w hw => haveI := hfin i; _root_.GlobalTheory.SphNonSplit.sphAU_of_not_split_m_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w hw
    embAV_inf := fun i P => by
      exact (congrArg (D.nbc.infW (X.nd.j i)) (A.au.wt _ _ _ _ (b i) (hb i).1)).symm }, ⟨{
    iotaQ := fun _ => rfl
    iotaQC := fun _ => rfl
    kFbar := hκ
    locW := fun _ _ _ => rfl
    satW := fun _ _ _ => rfl
    wdOf := fun _ _ _ _ => ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩
    muC := hμ
    S := F
    irr := irr
    inj := hinj
    surj := hsurj
    typeV := fun _ _ => rfl
    ptV := hptV
    emb := fun _ _ => rfl }⟩⟩
end
end
