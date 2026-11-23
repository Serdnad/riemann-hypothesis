module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle029
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle402
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle363
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle123
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle032
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle827
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle176
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle043
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle786
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle273
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle036
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle791
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem vector_at_split_place (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hC : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (S : Reading P.T)
    (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (hw : IsSplitPl D.host s.w) (hs : s.w = D.naut.plGw k v) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (hρ : CategoryTheory.Simple ρ) (hocc : PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ)) :
    ∃ x, IsBlockVec (S i s.w hw).mu ((S i s.w hw).rep PI).π x ∧ NotKilled ((S i s.w hw).rep PI).π (idemOf D k ρ) x := by
  classical
  have hrep := hT.rep i s hw PI
  rcases hrep with ⟨c, T, hc, hcs, -, -, -⟩
  obtain ⟨F, hF, hne⟩ := hocc
  set z := idemOf D k ρ with hz
  have hzc : ∀ b, z * b = b * z := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  have hcen := GlobalTheory.SeriesSupportTest.atPlace_central D k v z hzc
  obtain ⟨L, hLift, hCL⟩ := hC i
  have e : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dite_eq_left hcen]; exact hCL ⟨_, hcen⟩ F
  have hne' : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) ≠ 0 := by
    rw [← e]; intro h0; apply hne; exact (P.M.loc i).real_inj (h0.trans (map_zero _).symm)
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) =
      ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i PI k v s hs c hc hcs L hLift F hF h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hne'' : ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) ≠ 0 := by
    rw [hsum] at hne'
    simpa only [(hxs _).2.2] using hne'
  obtain ⟨U, hU, h1U, hθU⟩ := GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one _ D.R.r D.R.t (S i s.w hw).mu (S i s.w hw).mu_ok.1
  have hFS : (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i PI) := by
    have := hF; rw [P.H.av.typeV] at this; exact this
  obtain ⟨y, hy, hyz⟩ := GlobalTheory.T.local_component_continuous_iso_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i PI) (P.H.av.irr i PI) s
    ((S i s.w hw).rep PI).toIrrRep (hT.rep i s hw PI) c hc hcs (GlobalTheory.BlockType.blockGrp _ D.R.r D.R.t)
    (GlobalTheory.BlockType.blockChar (S i s.w hw).mu) U (fun h hh => hh.1) (GlobalTheory.BlockType.kOne_le_blockGrp _ _) hU h1U
    (fun g hg _ => hθU g hg) _ hFS (_root_.GlobalTheory.T.completion_iso_split_place_alt hL D P S hT i PI k v s hw hs c hc hcs F hF) _ xs (fun h => z.coeff h)
    (fun h => (hxs h).1) hne''
  refine ⟨y, GlobalTheory.BlockType.isBlockVec_of _ _ _ hy, fun h => Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV (xs h)), fun h => (hxs h).2.1, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact hyz
end GlobalTheory.DzVecLoc
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.OSplitBig
theorem exists_big_oSplit_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∃ big : D.what₂.places.Pl → Finset ℂ, ∀ (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C → GlobalTheory.SplitCoef.OSplit (withLoc L) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb
  classical
  have hsys := fun w => _root_.GlobalTheory.T.galois_family_local_global_alt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMt hstar hExp hsplit hCheb w
  choose FA Sy hSy using hsys
  have hexc := fun w : D.what₂.places.Pl => GlobalTheory.T.finite_exceptional_places_over_prime D (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)
  choose FB hFB using hexc
  let Fw : D.what₂.places.Pl → Finset (PlE D.host) := fun w => FA w ∪ FB w ∪ C.Q w
  let Pv : D.what₂.places.Pl → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → PlE D.host → Prop := fun w σ v =>
    v ∉ Fw w ∧ IsSplitPl D.host v ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B v ∧ IsFrob (F := D.host.E) B (normV v) σ
  let pw : D.what₂.places.Pl → (PlE D.host → ℕ → ℂ) → Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → ℂ[X] := fun w c σ =>
    if h : ∃ v, Pv w σ v then sysPol D c h.choose else 0
  have hcore := fun (w : D.what₂.places.Pl) (c : PlE D.host → ℕ → ℂ) =>
    GlobalTheory.T.exists_finite_splitting_set_frobeniusPolynomials (D.what₂.places.resChar w) (A.pl.ι w) D.host.E D.nd.Om D.R.nV (frobSet D (Fw w)) (pw w c)
      (dense_frobSet D hCheb (Fw w))
  choose SC hSC using hcore
  refine ⟨fun w => (Sy w).biUnion (SC w), ?_⟩
  intro L Sp hAut i x r hr
  obtain ⟨c, hcS, hc⟩ := hSy ((withLoc L).nd.w i) _ L Sp hAut i x rfl
  haveI : Fact ((withLoc L).nd.l i).Prime := (withLoc L).nd.lPrime i
  letI := (withLoc L).nd.dvrO i
  letI := (withLoc L).nd.algO i
  letI := (withLoc L).nd.finO i
  letI := (withLoc L).nd.topO i
  letI := (withLoc L).nd.trO i
  refine hSC ((withLoc L).nd.w i) c ((withLoc L).nd.l i) ((withLoc L).nd.w_l i) ((withLoc L).nd.O i) ((withLoc L).nd.O_adic i) (Sp.iq i) ?_ ?_ r
    hr.1 hr.2.1 ?_
  · exact fun z => Sp.iq_alg i z
  · intro z hz
    exact Sp.iq_big i z (Finset.mem_biUnion.2 ⟨c, hcS, hz⟩)
  · intro σ hσ
    have hex : ∃ v, Pv ((withLoc L).nd.w i) σ v := hσ
    have hspec := hex.choose_spec
    obtain ⟨hvF, hvs, B, hB, hFr⟩ := hspec
    have hvF' := hvF
    simp only [Fw, Finset.mem_union, not_or] at hvF'
    obtain ⟨⟨hvA, hvB⟩, hvQ⟩ := hvF'
    have hSO : SplitOut (withLoc L).nd i hex.choose := by
      have hQi : (withLoc L).nd.Q i = C.Q ((withLoc L).nd.w i) :=
        (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
      obtain ⟨h1, h2⟩ := hFB ((withLoc L).nd.w i) _ hvB
      refine ⟨hvs, ?_, ?_, ?_⟩
      · rw [← (withLoc L).nd.w_l i]; exact h1
      · intro hmem
        apply h2
        have := ((withLoc L).nd.S_def i _).1 hmem
        rw [← (withLoc L).nd.w_l i] at this
        exact this
      · show _ ∉ (withLoc L).nd.Q i
        rw [hQi]; exact hvQ
    refine (congrArg (Polynomial.map _) (hr.2.2 _ hSO B σ hB hFr)).trans ?_
    have hio : (qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i))).toRingHom.comp
        ((Sp.iq i).comp (algebraMap ((withLoc L).nd.O i) (FractionRing ((withLoc L).nd.O i)))) = iotaOC (withLoc L) i := by
      ext z
      simp only [iotaOC, RingHom.comp_apply]
      rw [show (withLoc L).naut.iotaQC i = L.Y.naut.iotaQC i from rfl, hAut.iotaQC i,
        show (withLoc L).naut.iotaQ i = L.Y.naut.iotaQ i from rfl, hAut.iotaQ i]
      rfl
    refine (congrArg (fun f => (heckePol (withLoc L).nd i x hex.choose).map f) hio).trans ?_
    rw [heckePol_map D L i x _ hSO]
    simp only [pw, dif_pos hex, sysPol]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc _ hvA k]
end GlobalTheory.OSplitBig
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowPointLoc
theorem main_alt_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) :
    GlobalTheory.SplitRead.RowPoint D.nd D.naut := by
  intro i σ hne
  obtain ⟨Q, hQ⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ :=
    GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D P.M P.H.hecke P.H.av P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D P) i σ Q hQ
  obtain ⟨hj, hw⟩ := (D.nd.locs_mem _ _ i').1 hi'
  have hl : D.nd.l i' = D.nd.l i := by rw [← D.nd.w_l i', ← D.nd.w_l i, hw]
  obtain ⟨φ, hφ⟩ := P.H.hecke.sameO i' i hj hw
  refine ⟨i', hj, hl, fun w _ => P.locW_eq i' i σ w, ⟨φ, ?_, fun z => (hφ z).symm⟩, P', x', hth, hx⟩
  exact continuous_of_adic (D.nd.O_adic i') (D.nd.O_adic i) φ
end GlobalTheory.RowPointLoc
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | exact _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | (intros; apply _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_signature_data_span_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.sigData_exists_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.sigData_exists_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.sigData_exists_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_weight_data_integral_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lattice_basis_free_module_place_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (hst : HkStab D T S In) (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host)
      [hfr : Module.Free (T.O i) ↥(BI D T S In i j b)] [hfi : Module.Finite (T.O i) ↥(BI D T S In i j b)], P ∉ T.S0 i →
      ∃ s : Multiset (FractionRing (T.O i)),
        (LinearMap.charpoly (hkB D T S In hst i j b k P)).map
          (algebraMap (T.O i) (FractionRing (T.O i))) = (s.map fun a => X - C a).prod := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.hkB_charpoly_splits_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.de_rham_weight_twist_character_alt : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ i : D.nd.Loc, (∀ a (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i χ w → (D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w ↔ D.naut.IsdRW i ρ w)) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i χ w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) w = D.naut.lpChar (D.naut.wdOf i ρ w) (D.naut.wdOf i χ w)) ∧ (∀ τ (c : ℤ), (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i χ w) → D.naut.jumpsW i χ τ = {c} → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (D.naut.jumpsW i ρ τ).map (· + c))) := by
  first | exact @_root_.GlobalTheory.TwistGal.galois_twist_alt | exact _root_.GlobalTheory.TwistGal.galois_twist_alt | (intros; apply _root_.GlobalTheory.TwistGal.galois_twist_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_trace_frobenius_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  first | exact @_root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt | exact _root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt | (intros; apply _root_.GlobalTheory.AutPart.heckePol_map_eq_frobPol_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem _root_.GlobalTheory.T.galois_family_hecke_compatible_alt : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (μ : D.naut.CG 1), D.naut.csd μ → (∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j) → ∀ w, SplitOut X.nd i w → D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) ∧ ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2)) = {(qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i)))} := by
  first | exact @_root_.GlobalTheory.AutPart.chiMu_unr_frob_alt | exact _root_.GlobalTheory.AutPart.chiMu_unr_frob_alt | (intros; apply _root_.GlobalTheory.AutPart.chiMu_unr_frob_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.PtExt

theorem main_alt_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ i₁ : L₁.lay.fixZ.nd.Loc, ∃ i₀ : L₀.lay.fixZ.nd.Loc, L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ ∧ L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ ∧ ∃ e : L₁.lay.fixZ.nd.X i₁ ≃ L₀.lay.fixZ.nd.X i₀, ∀ (v : PlE D.host) (k : ℕ) (x : L₁.lay.fixZ.nd.X i₁), SplitOut L₁.lay.fixZ.nd i₁ v → 1 ≤ k → k ≤ D.R.nV → iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ ((L₁.lay.fixZ.nd.hT i₁ v k : L₁.lay.fixZ.nd.X i₁ → L₁.lay.fixZ.nd.O i₁) x) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ ((L₀.lay.fixZ.nd.hT i₀ v k : L₀.lay.fixZ.nd.X i₀ → L₀.lay.fixZ.nd.O i₀) (e x)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₁
  have onto : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 →
      ∀ c ∈ EigSet (M (D.what₂.muTw w) j h1 h2) (D.what₂.places.resChar w) (C.Q w),
        ∃ i ∈ L.X.nd.locs j w, ∃ x : L.X.nd.X i, sys L i x = c := by
    intro big L hB j w h1 h2 htw c hc
    obtain ⟨i, hi, x, hx⟩ := _root_.GlobalTheory.T.side_eigen_frobenius_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hch hmt hstar hexp hspl hcheb big L hB j w h1 h2 htw c hc
    refine ⟨i, hi, x, funext fun v => funext fun k => ?_⟩
    by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
    · rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, hx v k hg]
    · rw [_root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi x hg, hc.1 v k hg]
  have cong : ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
      ∀ (j : ℕ) (w : D.what₂.places.Pl) (i i' : L.X.nd.Loc), i ∈ L.X.nd.locs j w → i' ∈ L.X.nd.locs j w →
      ∀ (x : L.X.nd.X i) (x' : L.X.nd.X i'),
        (i = i' ↔ ∀ v k, sys L i x v k - sys L i' x' v k ∈ (A.pl.plB w).nonunits) := by
    intro big L hB j w i i' hi hi' x x'
    rw [_root_.GlobalTheory.T.locations_distinguished_by_generics_alt D cf jE A M C tp.tup big L hB j w i i' hi hi' x x']
    constructor
    · intro h v k
      by_cases hg : GenAt D (D.what₂.places.resChar w) (C.Q w) v k
      · rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi' x' hg]; exact h v k hg
      · rw [_root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi x hg, _root_.GlobalTheory.PtExt.sys_eq_zero_of_not_gen_at hB hi' x' hg, sub_zero]; exact zero_mem _
    · intro h v k hg
      rw [← _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi x hg, ← _root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB hi' x' hg]; exact h v k
  have h1 := (L₁.X.nd.j_range i₁).1
  have h2 := (L₁.X.nd.j_range i₁).2
  have hi₁ : i₁ ∈ L₁.X.nd.locs (L₁.X.nd.j i₁) (L₁.X.nd.w i₁) := (L₁.X.nd.locs_mem _ _ i₁).2 ⟨rfl, rfl⟩
  have htw : D.what₂.muAt (L₁.X.nd.w i₁) ≠ D.what₂.mu0 := L₁.X.nd.w_tw i₁
  obtain ⟨x₁⟩ := L₁.X.nd.neX i₁
  obtain ⟨i₀, hi₀, y₀, hy₀⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₁ h1 h2 hi₁ x₁)
  have fwd : ∀ x : L₁.X.nd.X i₁, ∃ y : L₀.X.nd.X i₀, sys L₀ i₀ y = sys L₁ i₁ x := by
    intro x
    obtain ⟨i', hi', y', hy'⟩ := onto big₀ L₀ hB₀ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₁ h1 h2 hi₁ x)
    have hc : i' = i₀ := by
      rw [cong big₀ L₀ hB₀ _ _ i' i₀ hi' hi₀ y' y₀, hy', hy₀]
      exact (cong big₁ L₁ hB₁ _ _ i₁ i₁ hi₁ hi₁ x x₁).1 rfl
    subst hc
    exact ⟨y', hy'⟩
  choose f hf using fwd
  have finj : Function.Injective f := fun x x' h => sys_inj L₁ i₁ (by rw [← hf x, ← hf x', h])
  have fsurj : Function.Surjective f := by
    intro y
    obtain ⟨i', hi', x', hx'⟩ := onto big₁ L₁ hB₁ _ _ h1 h2 htw _ (_root_.GlobalTheory.PtExt.sys_mem_eig_set_of_built hB₀ h1 h2 hi₀ y)
    have hc : i' = i₁ := by
      rw [cong big₁ L₁ hB₁ _ _ i' i₁ hi' hi₁ x' x₁, hx', ← hy₀]
      exact (cong big₀ L₀ hB₀ _ _ i₀ i₀ hi₀ hi₀ y y₀).1 rfl
    subst hc
    exact ⟨x', sys_inj L₀ i₀ (by rw [hf x', hx'])⟩
  have hw₀ : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).2
  have hj₀ : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := ((L₀.X.nd.locs_mem _ _ i₀).1 hi₀).1
  refine ⟨i₀, hw₀, hj₀, Equiv.ofBijective f ⟨finj, fsurj⟩, fun v k x hv k1 k2 => ?_⟩
  have hg := (_root_.GlobalTheory.PtExt.splitOut_iff_genAt_alt hB₁ hi₁ v k).1 ⟨hv, k1, k2⟩
  have e := congrFun (congrFun (hf x) v) k
  rw [_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB₀ hi₀ _ hg] at e
  exact (_root_.GlobalTheory.PtExt.sys_eq_iota_of_gen_at hB₁ hi₁ x hg).symm.trans e.symm
end GlobalTheory.PtExt
end
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.RowEx
open Formalism.L2.Host (HChar)
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl
namespace GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
def extensionWithAtProperty (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (A : AtP) : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL := fun K B f T w Z Wt p0 t nch n xd c =>
  N K B f T w Z Wt p0 t nch n xd c × PLift (A K B f T)
end GlobalTheory.Mem.LiteralAutomorphy
end
end
end
