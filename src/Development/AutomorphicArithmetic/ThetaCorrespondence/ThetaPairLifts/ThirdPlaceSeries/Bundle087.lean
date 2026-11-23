module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle016
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle017
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle015
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle018
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle014
public import Formalism.LocalToGlobal.IndefiniteReal.IsThPKernelSigBase
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle065
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2400
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem

@[expose] public section

section



section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
private theorem emb_cj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    (τ : E →+* PadicAlgCl l) :
    io.toRingHom.comp (GlobalTheory.ExpFrame.cj τ) = ComplexEmbedding.conjugate (io.toRingHom.comp τ) := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E (io.toRingHom.comp τ) x
private theorem places_inj_pz {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    {ι : Type} {inc : ι → (E →+* PadicAlgCl l)} (h : IsHalf inc) :
    Function.Injective fun τ => InfinitePlace.mk (io.toRingHom.comp (inc τ)) := by
  intro τ τ' e
  have hi : ∀ a b : E →+* PadicAlgCl l, io.toRingHom.comp a = io.toRingHom.comp b → a = b := fun a b hab =>
    RingHom.ext fun x => io.injective (RingHom.congr_fun hab x)
  rcases InfinitePlace.mk_eq_iff.1 e with e | e
  · exact h.1 (hi _ _ e)
  · exact absurd (hi _ _ ((emb_cj_pz io _).trans e)) (h.2.1 τ τ')

private theorem frame_embedding_exists {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hmu : ∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res N (mu τ))) (hθ : F.IsEig mu θ) :
    ∃ π : Submodule ℂ (UA D.host.E N → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧
        (∀ v, GlobalTheory.Hk3.Good p.R.toRealDat t v → ∀ x ∈ locU N v, cLoc v x ∈ GlobalTheory.LFun.KGL v (n := N) → RU D.host.E N x φ = φ) ∧
        ∀ Q : (blk p j t).Pl, (∀ x ∈ locU N (labOf p j t Q), cLoc (labOf p j t Q) x ∈ GlobalTheory.LFun.KGL (labOf p j t Q) (n := N) →
          RU D.host.E N x φ = φ) ∧
        ∀ i, (ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E N).comp (locU N (labOf p j t Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j t Q) (n := N)).comap ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j t Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab N (ix i).2))
              ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype x)) φ = T.io (θ i) • φ := by
  subst hN
  classical
  have hs : (Vc D j).SigOK := D.sp.V_sig _
  have hp : (Vc D j).IsPosDef := p.vpos j
  have hinf : Formalism.L2.Theta.IsInfFam p.R.θ := p.charW.base.models.inf
  obtain ⟨jj, h₀, hTr⟩ := GlobalTheory.DefTransfer.exists_isTransfer D (Vc D j) p.R.θ hinf hs hp
  obtain ⟨B, hB1, hB2⟩ := UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary D (Vc D j) hs hp jj hTr.2.1
  obtain ⟨Fm, hF0, hFl, hFr, hFh⟩ := UpperTheory.exists_nonzero_vectorValued_eigenform_unitary p j t F e0 ix inc T mu θ hθ
  have hb : ∀ τ, T.io.toRingHom.comp (e0.comp (Links.labLL D τ)) = Formalism.BasicNotions.TH.tauE D τ := fun τ => by
    rw [← Formalism.IndefR.Conj.labE_base τ]
    exact RingHom.ext fun x => T.liftFrame_embedding_base _
  have hemb : ∀ τ, T.io.toRingHom.comp (inc τ) = Formalism.BasicNotions.TH.tauE D τ ∨
      T.io.toRingHom.comp (inc τ) = ComplexEmbedding.conjugate (Formalism.BasicNotions.TH.tauE D τ) := fun τ => by
    rcases T.lab τ with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, emb_cj_pz, hb])
  have hfix : ∀ (k : Formalism.L2.Theta.GA D (Vc D j)), (∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t,
      levChi p j t ⟨_, h⟩ = 1) → ∀ g, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k) = Fm g := by
    rintro k ⟨h, h1⟩ g
    have := hFr ⟨_, h⟩ g
    rw [h1, Units.val_one, one_smul] at this
    exact this
  have hev : ∀ᶠ κ in nhds (1 : Formalism.L2.Theta.GA D (Vc D j)), ∀ g,
      Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict κ) = Fm g :=
    (GlobalTheory.ThetaIntegrand.eventually_level (Vc D j) (p.R.βV j) (p.R.datVt j t)).mono fun κ h => hfix κ h
  obtain ⟨F1, h10, h1l, h1i, h1e, A, hA⟩ := UpperTheory.vectorValued_autForm_equivariant_infinite_component D (Vc D j) p.R.θ jj h₀ hinf hTr
    (fun τ => T.io.toRingHom.comp (inc τ)) hemb mu T.sh Fm hF0 hFl hev
  let lam : D.what₂.Tau → DomWeight (Vc D j).rank := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + T.sh τ, fun a b hab => add_le_add_left (Int.ofNat_le.2 (hmu τ hab)) _⟩
  obtain ⟨π, hπ, hw, φ, hφ, hφ0, hsum⟩ := UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued D.host.E (Vc D j).rank D.what₂.Tau (fun τ => T.io.toRingHom.comp (inc τ))
    (places_inj_pz T.io T.half) mu T.sh lam (fun _ _ => rfl) B hB1 hB2 F1 h10 h1l h1i h1e
  have htr : ∀ g y, F1 (g * y) = A (Fm ((Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (jj g * h₀) *
      (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (GlobalTheory.DefTransfer.cj jj h₀ y))) := fun g y => by
    rw [hA, ← map_mul, GlobalTheory.DefTransfer.cj_apply, map_mul jj]
    congr 3
    group
  have hK : ∀ v v', GlobalTheory.Hk3.Good p.R.toRealDat t v' → GlobalTheory.Hk3.hyp (Vc D j) v = GlobalTheory.Hk3.hyp (Vc D j) v' →
      ∀ x ∈ GlobalTheory.DefTransfer.KP (Vc D j).rank v, RU D.host.E (Vc D j).rank x φ = φ := by
    intro v v' hg he x hx
    have h1 := (hTr.2.2.2.2.2.2.1 v x).2 hx
    rw [he] at h1
    have h2 := hfix _ (UpperTheory.levChi_eq_one_of_good_place p j t v' hg _ h1)
    have := hsum Unit Finset.univ (fun _ => x) 1 (fun _ _ => hx.1.1) fun g => by
      rw [Finset.univ_unique, Finset.sum_singleton, one_smul, htr, h2, hA]
    simpa using this
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun _ => rfl, hw τ, ?_⟩, φ, hφ, hφ0, fun v hv x h1 h2 => hK v v hv rfl x ⟨h1, h2⟩, fun Q => ?_⟩
  · rw [emb_cj_pz]
    exact GlobalTheory.DefU.AU.HasWt.conjugate (π := GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) (hw τ)
  have hg : GlobalTheory.Hk3.Good p.R.toRealDat t (plOf p j t Q) :=
    ((GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
      p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2).1
  have hKQ := hK (labOf p j t Q) _ hg (GlobalTheory.SphConj.hyp_conj _ _)
  refine ⟨fun x h1 h2 => hKQ x ⟨h1, h2⟩, fun i hi => ?_⟩
  subst hi
  obtain ⟨r1, r2, -⟩ := (T.ix_range (ix i)).1 ⟨i, rfl⟩
  obtain ⟨hloc, R, hR, hRs⟩ := UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace p j t (ix i).1 (ix i).2 r1 r2
  rw [GlobalTheory.SplitTransfer.heckeVec_divInd hTr hKQ hR]
  refine hsum _ R (fun γ => (GlobalTheory.DefTransfer.cj jj h₀).symm γ) _ (fun γ hγ => ((hTr.2.2.2.2.2.2.2 _ _ R hR).1 γ hγ).1.1) fun g => ?_
  simp only [htr, MulEquiv.apply_symm_apply]

  rw [← map_sum, hRs _ Fm hFr, hA, ← map_smul]
  exact congrArg A (hFh i hloc _)
theorem _root_.GlobalTheory.T.small_place_prime_local_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W hD _ w hw hW _ _ F R inc T mu θ hmu hθ
  obtain ⟨π, h1, h2, φ, h3, h4, h5, h6⟩ := frame_embedding_exists p j (p.R.mu w) hD.Nr F R.e0 R.ix inc T mu θ hmu hθ
  exact ⟨π, h1, h2, fun v hv => ⟨φ, h3, h4, h5 v (UpperTheory.good_place_of_twist_place_dividing p j P W hD w hw hW v hv)⟩, φ, h3, h4, fun Q _ => h6 Q⟩
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.RowsParts
variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}
end GlobalTheory.Fc.RowsParts
namespace GlobalTheory.Fc
open RowsParts
theorem row_rRows_of_parts_alt : ∀ (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), Row Q Lk (fun 𝒜 σ => ∃ τ : _root_.GlobalTheory.Fc.CompatibleSelection σ, Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL3Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandNormBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.summandL6Bound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ) ∧ Ind.EvWC (fun Fm => DIVinN Fm) _root_.GlobalTheory.Fc.Ind.summandFunctionalBound 𝒜 (_root_.GlobalTheory.Fc.summandSelection σ τ)) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE) → Row Q Lk (Ind.EvW (Bd := _root_.GlobalTheory.Fc.BundleCondition) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P) → Row Q Lk (Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => DR D O c b C CH) → _root_.GlobalTheory.Fc.R1.SlotDefiniteRowsCondition DR Q Lk := by
  intro DR Q Lk h1 h2 h3 h4
  refine (h1.and (h2.and (h3.and h4))).imp fun 𝒜 σ _ H => ?_
  obtain ⟨⟨τ, hS, hL3, hON, hL6, hFUN⟩, hM, hK, hD⟩ := H
  have hw : ∀ {eps : ℝ} (Fm : FamP eps), GlobalTheory.Cp.D3 3 𝒜 Fm → W3 𝒜 Fm :=
    fun Fm h => (working_classes_frozen.1 𝒜 _ Fm).2.1 h
  have hall := Closed.and hS (Closed.and hL3 (Closed.and hON (Closed.and hL6 (Closed.and hFUN
    (Closed.and hM (Closed.and hK hD))))))
  refine Closed.imp (Pk.Closed.sub hall hw) fun Fm CH _ H hc => ?_
  obtain ⟨hS, hL3, hON, hL6, hFUN, hM, hK, hD⟩ := H
  have hc' := hw Fm hc
  obtain ⟨C1, p1, hS⟩ := hS hc' trivial
  obtain ⟨C2, -, hL3⟩ := hL3 hc' trivial
  obtain ⟨C3, -, hON⟩ := ev_prem (hON hc')
  obtain ⟨C4, -, hL6⟩ := hL6 hc' trivial
  obtain ⟨C5, -, hFUN⟩ := ev_prem (hFUN hc')
  obtain ⟨C6, -, hD⟩ := hD hc' trivial
  obtain ⟨C, k1, k2, k3, k4, k5, k6⟩ : ∃ C : ℝ, C1 ≤ C ∧ C2 ≤ C ∧ C3 ≤ C ∧ C4 ≤ C ∧ C5 ≤ C ∧ C6 ≤ C :=
    ⟨max C1 (max C2 (max C3 (max C4 (max C5 C6)))), by simp, by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨x1, hS⟩ := hS C k1
  obtain ⟨x2, hL3⟩ := hL3 C k2
  obtain ⟨x3, hON⟩ := hON C k3
  obtain ⟨x4, hL6⟩ := hL6 C k4
  obtain ⟨x5, hFUN⟩ := hFUN C k5
  obtain ⟨x6, hD⟩ := hD C k6
  obtain ⟨x7, hM⟩ := hM hc'
  obtain ⟨x8, hK⟩ := hK hc'
  obtain ⟨x0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :
      ∃ y : ℝ, x1 ≤ y ∧ x2 ≤ y ∧ x3 ≤ y ∧ x4 ≤ y ∧ x5 ≤ y ∧ x6 ≤ y ∧ x7 ≤ y ∧ x8 ≤ y :=
    ⟨max x1 (max x2 (max x3 (max x4 (max x5 (max x6 (max x7 x8)))))),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨C, p1.trans k1, x0, fun x hx _ hle i => ⟨?_, hD x hx (l6.trans hle) i⟩⟩
  have s := hS x hx (l1.trans hle) i
  exact
    { w1 := s.1
      covol := hL3 x hx (l2.trans hle) i
      onto := hON x hx (l3.trans hle) i
      lamLow := fun _ => hL6 x hx (l4.trans hle) i
      seeIso := s.2.1
      miStar := hM x hx (l7.trans hle) i
      fun0 := hFUN x hx (l5.trans hle) i
      pass := s.2.2
      kap := hK x hx (l8.trans hle) i }
end GlobalTheory.Fc
end
end

section



section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem lifts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop} (h : _root_.GlobalTheory.CovTop.LiftsCondition Q) (h' : _root_.GlobalTheory.CovTop.LiftsCondition Q') :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP _ => (∃ C, Q Fm x hx ι p i PP C) ∧ ∃ C, Q' Fm x hx ι p i PP C :=
  Closed.imp (Closed.and h h') fun _ _ _ ⟨⟨C, _, a⟩, C', _, b⟩ => ⟨0, le_rfl, (a.and b).imp fun _ h x hx hle ι p hp i =>
    ⟨⟨C, (h x hx hle ι p hp).1 i⟩, C', (h x hx hle ι p hp).2 i⟩⟩
end GlobalTheory.CovTop.ShareRowsNef
end
end
end

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
noncomputable section
namespace GlobalTheory.CovTop.DgShare
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem lifts_and_alt {Q Q' : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop} (h : _root_.GlobalTheory.CovTop.LiftsCondition Q) (h' : _root_.GlobalTheory.CovTop.LiftsCondition Q') :
    _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x hx ι p i PP _ => (∃ C, Q Fm x hx ι p i PP C) ∧ ∃ C, Q' Fm x hx ι p i PP C :=
  Closed.imp (Closed.and h h') fun _ _ _ ⟨⟨C, _, a⟩, C', _, b⟩ => ⟨0, le_rfl, (a.and b).imp fun _ h x hx hle ι p hp i =>
    ⟨⟨C, (h x hx hle ι p hp).1 i⟩, C', (h x hx hle ι p hp).2 i⟩⟩
end GlobalTheory.CovTop.DgShare
end
end
end

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

noncomputable section
namespace GlobalTheory.BadEmb
section Abstract
variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)
end Abstract
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
end General
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weights
theorem lifts_of_four_quantitative_conditions {Q₁ Q₂ Q₃ Q₄ R : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop}
    (h₁ : _root_.GlobalTheory.CovTop.LiftsCondition Q₁) (h₂ : _root_.GlobalTheory.CovTop.LiftsCondition Q₂) (h₃ : _root_.GlobalTheory.CovTop.LiftsCondition Q₃) (h₄ : _root_.GlobalTheory.CovTop.LiftsCondition Q₄)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
      (PP C₁ C₂ C₃ C₄ : ℝ), Q₁ Fm x hx ι p i PP C₁ → Q₂ Fm x hx ι p i PP C₂ → Q₃ Fm x hx ι p i PP C₃ →
      Q₄ Fm x hx ι p i PP C₄ → R Fm x hx ι p i PP 0) : _root_.GlobalTheory.CovTop.LiftsCondition R := by
  refine (((h₁.and h₂).and h₃).and h₄).imp fun Fm CH _ h' => ?_
  obtain ⟨⟨⟨⟨_, -, a1⟩, _, -, a2⟩, _, -, a3⟩, _, -, a4⟩ := h'
  obtain ⟨x0, h'⟩ := ((a1.and a2).and a3).and a4
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h' x hx hle ι p hp
  exact h Fm x hx ι p i _ _ _ _ _ (b1 i) (b2 i) (b3 i) (b4 i)
end GlobalTheory.BadEmb
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_onPt_of_guarded_alt (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP)
    (h : Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p)
    (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜) (hd : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm)
    (hR : EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ) (hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint G) 𝒜 σ) : EvWC prem (fun C CH => _root_.GlobalTheory.Fc.Ind.conditionOnPoint (T C CH)) 𝒜 σ := by
  have h' : Closed (W3 𝒜) fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p := by
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties 𝒜 _ Fm hc (hd _ Fm (w3_a hc))) hL⟩
  refine Closed.imp (Closed.and h' (Closed.and hR hG)) ?_
  rintro eps Fm CH - ⟨h1, h2, h3⟩ hc hp
  obtain ⟨C0, hC0, a, ha⟩ := h1 hp
  obtain ⟨b, hb⟩ := h2 hc
  obtain ⟨c, hc'⟩ := h3 hc
  refine ⟨C0, hC0, fun C hC => ⟨max a (max b c), fun x hx hle i => ?_⟩⟩
  have e1 : a ≤ x := (le_max_left _ _).trans hle
  have e2 : b ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have e3 : c ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  exact ha x hx e1 i (σ Fm (w3_a hc) x hx i).pt (hb x hx e2 i) (hc' x hx e3 i) C hC
end GlobalTheory.Fc.Ind
end
end

section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR
end GlobalTheory.BaseLevelInj

open GlobalTheory.BaseLevelInj in
theorem GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g hg
  obtain ⟨κ, hlift, happ⟩ := (p.pins i).2.lift.lev (g : p.P.Gp)
  have hβ := p.charW.base.lev.βW i
  have hSt := Formalism.L2.DIV.parLev_St hlift.2.1
  have hfc := GlobalTheory.LevelAction.finCong_of_mem_St hβ hSt
  have hι := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hMb : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
    have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← p.T.Q.l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left : p.T.Q.l.Mb * _ ≤ p.T.Q.l.Mb) h0
  have h4 := GlobalTheory.T.levelMove_lift_congruent_mod_ideal (Wc D i) (iotaW p.T i) hι p.T.Q.l.M p.T.Q.l.Mb (Mfr p.T.Q.l) p.T.Q.l.coprime hMb κ hfc
    ((p.O i).lev (g : p.P.Gp)) happ hg
  have h3 := GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice (Wc D i) _ _ h4
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at h3
  have h2 := hatL_cong_of_hat (Wc D i) κ _ _ h3
  have hfr : Formalism.L2.DIV.IsFrame (p.R.βW i) (p.R.ΛW i) := by obtain ⟨c, h, -⟩ := hβ; exact h
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hred : ∀ PP ∈ p.R.Pg, Formalism.L2.DIV.redFn (p.R.βW i) PP (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    refine GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal _ _ _ hfr hSt _ h2 PP ?_
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  have hT1 : Formalism.L2.DIV.rTup (p.R.βW i) (p.R.datWp i p.R.triv) (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (p.R.βW i) PP.1 _) = 1
    rw [hred PP.1 PP.2]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  have he : p.R.eG (g : p.P.Gp) = 1 := by rw [← hlift.2.2]; exact hT1
  have : (g : p.P.Gp) = 1 := by rw [← map_one p.R.eG] at he; exact p.R.eG.injective he
  exact Subtype.ext this
end
end

section



section
set_option autoImplicit false

noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.RefSum.SizeTZ
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
end Free
variable {D : D7}
variable {L : SizeData₂ D} {P : ParameterChoice' D L}
theorem parameters_scale_rank_gap_bounds : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (lenT p i PP : ℝ) * zBase (Fm.L x ι) ^ 12 ≤ unitE p ∧ 1 ≤ (Fm.L x ι).sc.L ∧ lrd (Fm.D x ι).host.E ≤ 3 * (Fm.L x ι).sc.L ∧ (nCol (dat p i) : ℝ) ≤ 20 * (Fm.D x ι).R.f * (Fm.D x ι).R.r ^ 2 ∧ 1 ≤ (Fm.D x ι).R.f ∧ 1 ≤ (Fm.D x ι).R.r := fun h =>
  Closed.imp h fun Fm _ _ ⟨C, h0, a, h⟩ => ⟨C, h0, a, fun x hx hle ι p hp i =>
    ⟨(lenT_mul_le_b p i (Fm.parT x hx ι)).1.trans (h x hx hle ι p hp i).2.1, one_le_scL _, lrd_le (Fm.params x hx ι),
      (lenT_mul_le_b p i (Fm.parT x hx ι)).2,
      le_trans one_le_two (two_le_f _), le_trans (by norm_num) (six_le_r _)⟩⟩
end GlobalTheory.RefSum.SizeTZ
end
end
end
