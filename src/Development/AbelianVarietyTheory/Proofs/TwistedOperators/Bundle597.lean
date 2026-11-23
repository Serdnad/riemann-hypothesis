module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle515
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle560
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle188
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle362
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle576
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle586
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OffPlacesPartMovedLevelKeepsStandardHomLattice
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle003
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle015
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLinF
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle014
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle324
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.AlgebraMapAEEqZero

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

theorem _root_.GlobalTheory.T.fockVacuumEquations_transfer_schroedingerDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  first | exact @GlobalTheory.VacTransfer.vacDatum_transfer | exact GlobalTheory.VacTransfer.vacDatum_transfer | (intros; apply GlobalTheory.VacTransfer.vacDatum_transfer <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
noncomputable section

namespace GlobalTheory.TopLevelInv

section Unr

variable {D : D7}

theorem unrOff_mul' {e : AE D} {χ χ' : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ)
    (h' : Formalism.IndefR.Fin.UnrOff e χ') : Formalism.IndefR.Fin.UnrOff e (χ * χ') :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, one_mul]

theorem unrOff_inv' {e : AE D} {χ : (AE D)ˣ →* Circle} (h : Formalism.IndefR.Fin.UnrOff e χ) :
    Formalism.IndefR.Fin.UnrOff e χ⁻¹ :=
  fun x h1 h2 h3 h4 => by rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

theorem pg_near_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    {PP : Pl D.host.E} (h : PP ∈ L.Pg) : ∃ w ∈ locPl G t, PP = w ∨ PP = GlobalTheory.IdemSupport.cP w := by
  classical
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 h
  have hm := GlobalTheory.LevelRamif.typePrime_mem hk
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hv
  have hvk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  have hS1 : v ∈ S1 D := by
    rw [S1_mem_OmF]
    fin_cases k
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  have hS0 : v ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)
  refine ⟨G.pl.w v, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hS0), ?_⟩
  exact GlobalTheory.IdemSupport.eq_or_eq_cP (by rw [G.pl.under_w hS0])

theorem conjPrime_conjPrime₂ (P : HeightOneSpectrum (𝓞 D.host.E)) : GlobalTheory.IdemSupport.cP (GlobalTheory.IdemSupport.cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO])

theorem unrOff_mu_locPl {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {t μ₀ : T}
    (hL : L.Is μ₀) (j : Fin D.R.m) {e : AE D} (he : IsIdemSum e (locPl G t)) :
    Formalism.IndefR.Fin.UnrOff e (L.mu t ((j : ℕ) + 1)) ∧ Formalism.IndefR.Fin.UnrOff e L.eta := by
  classical
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t j
  have hmu : Formalism.IndefR.Fin.UnrOff e (L.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.mu0 j) he fun PP' h1 h2 => by
      refine h4 PP' (fun h => ?_) fun PP h h' => ?_
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        rcases hw' with rfl | rfl
        · exact h1 hw
        · exact h2 w hw ((GlobalTheory.IdemSupport.isConjPl_iff _ _).2 rfl)
      · obtain ⟨w, hw, hw'⟩ := pg_near_locPl G hL t h
        have e1 := (GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h'
        rcases hw' with rfl | rfl
        · exact h2 PP hw h'
        · rw [conjPrime_conjPrime₂] at e1
          exact h1 (e1 ▸ hw)
  have hxi : Formalism.IndefR.Fin.UnrOff e (L.xi t) :=
    GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e (hL.xi t) he fun PP' h1 h2 => by
      by_contra hn
      rcases (hL.Q_ram t PP').1 hn with h | ⟨PP, h, h'⟩
      · exact h1 (Finset.mem_union_right _ h)
      · exact h2 PP (Finset.mem_union_right _ h) h'
  exact ⟨unrOff_mul' hmu hxi, GlobalTheory.ChrOff.unrOff_of_unrAt D _ _ (locPl G t) e hL.eta he fun PP' _ _ => L.C.isEta.unr PP'⟩

end Unr



theorem vacFix_conjPt_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m)
    (k : FinPt G (.top (j + 1))), finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj →
    ∀ e : AE D, IsIdemSum e (locPl G t) → ∀ ε : AF D.host.F, IsIdempotentElem ε →
    algebraMap (AF D.host.F) (AE D) ε = e + cA D e →
    W.om (.top t j) (1, resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) (S.Z.vac (.top t j)) =
      S.Z.vac (.top t j) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he ε hε halg
  have hε' : IsIdempotentElem (1 - ε) := hε.one_sub
  have hdp : DefPair D.R.m (.top t j : Pair T) := by show j + 1 ≤ D.R.m; omega
  have hW := W.om_is (.top t j) (by simp only [Pair.InRange, Node.InRange]; omega)
  have hv := S.Z.vac_is _ hdp
  have hdS : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hdT : DefNode D.R.m (.top (j + 1)) := by show j + 1 ≤ D.R.m; omega
  have hS := S.N.selfDual (X := .top j) hdS
  have hT := S.N.selfDual (X := .top (j + 1)) hdT
  have hfS := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top j))) (G.Λ (.top j)) (S.βp j)
    (Lev.finE (G.V (.top j)) (S.N.u (.top j)).1) (S.βp_is j hdS) (S.N.u_lat _ hdS)
  have hfT := GlobalTheory.OffPartLattice.isFrame_moved (colLat (S.N.fr (.top (j + 1)))) (G.Λ (.top (j + 1))) (S.βp (j + 1))
    (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (S.βp_is (j + 1) hdT) (S.N.u_lat _ hdT)
  have hrkS : (G.V (.top j)).rank = rankX D j := (G.isV (X := .top j) hdS fun _ e => by cases e).rank
  have hrkT : (G.V (.top (j + 1))).rank = rankX D (j + 1) := (G.isV (X := .top (j + 1)) hdT fun _ e => by cases e).rank
  have hrk : (G.V (.top j)).rank ≠ (G.V (.top (j + 1))).rank := by
    intro h
    rw [hrkS, hrkT] at h
    simp only [rankX, add_mul, one_mul] at h
    omega
  have hev : Even (G.V (.top j)).rank := hrkS ▸ even_rankX D j
  obtain ⟨hμ, hη⟩ := unrOff_mu_locPl G hL ⟨j, by omega⟩ he
  have hatt : ∀ n, Formalism.IndefR.Fin.UnrOff e (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) := by
    intro n
    unfold Formalism.IndefR.Lift.attChr
    split_ifs
    · exact unrOff_mul' hμ (unrOff_inv' hη)
    · exact hμ
  have hn : ∃ (μ : Measure (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (𝓕 : Set (WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))),
      IsCovolOne (ratL (G.pT (.top t j : Pair T)) (G.pS (.top t j : Pair T))) μ 𝓕 ∧
        nrm2 μ 𝓕 (S.Z.vac (.top t j)) = 1 := by
    obtain ⟨⟨p, hp⟩, hall⟩ := hv.2.norm
    exact ⟨p.1, p.2, hp, hall p hp⟩

  have hf := GlobalTheory.ExpansionInvariance.idem_conj_sum (GlobalTheory.PlaceVec.idemSum_mul_self he) he.2
  have h2 := GlobalTheory.ExpansionInvariance.idem_compl hf
  have hcut : resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k) =
      GlobalTheory.ExpansionInvariance.cutPart (1 - (e + cA D e)) (G.V (.top (j + 1))) (conjPt S j k) := by
    apply Formalism.IndefR.Fin.LevelGroupLemmas.gaExt
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG _ hε', GlobalTheory.ExpansionInvariance.mt_cutPart h2.1 h2.2, map_sub, map_one, halg]
    unfold Formalism.IndefR.Fin.LevelGroupLemmas.resM
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hSt : Lev.finE (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) ∈
      St ((Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1)⁻¹ * S.βp (j + 1)) := by
    have hk2 : finG (G.V (.top (j + 1))) k ∈ prodLev (S.βp (j + 1)) (locPl G t) (fun w => topRank_eq G t w hj.le)
        (fun w => (S.term t Φ β w).pr _ j.succ_pos hj) := hk
    rw [hcut]
    exact GlobalTheory.OffPartLattice.finE_cut_mem_St (G.V (.top (j + 1))) (S.βp (j + 1))
      (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1) (finG (G.V (.top (j + 1))) k) (conjPt S j k)
      (by simp only [conjPt, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]; rfl) he (fun Q hQ => by
        have h3 := (Subgroup.mem_inf.1 hk2).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 Q
        rw [Subgroup.mem_iInf] at h4
        exact Subgroup.mem_comap.1 (h4 hQ))
  have hP : ∀ a b, (e + cA D e) * (mt (G.V (.top (j + 1))) (resG (G.V (.top (j + 1))) (1 - ε) (conjPt S j k)) - 1) a b = 0 := by
    intro a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_resG_sub hε' _ a b, ← mul_assoc, map_sub, map_one, halg]
    have h0 : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
      linear_combination (-1 : AE D) * hf.1
    rw [h0, zero_mul]
  exact Formalism.IndefR.Fin.LevelGroupLemmas.vacFixOff (Formalism.IndefR.Fin.splitLinF D) (Formalism.IndefR.Fin.placeModelAtF D)
    (Formalism.IndefR.Fin.splitOrInert D) W.ψ _ _ _ _ _ hW (GlobalTheory.InertAll.inertAllO D _ _ _ _ _ _ hW) hrk (Or.inl hev) _ _ hS hT _ _
    hfS hfT (locPl G t) e he (hatt _) (hatt _) _ hv.2.theta hv.2.lat hn 1 _ (one_mem _)
    (Formalism.IndefR.Fin.LevelGroupLemmas.resG_mem_GfC _ hε' (SetLike.coe_mem _)) (by rw [map_one]; exact one_mem _) hSt
    (fun a b => by rw [Formalism.IndefR.Fin.LevelGroupLemmas.mt_one', sub_self, Matrix.zero_apply, mul_zero]) hP

end GlobalTheory.TopLevelInv
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobalPair.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl (F := F)))
  (hvac : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v))
  (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hvac

theorem ext_mem_SB (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl (F := F)) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact hvac v


omit hvac in
include hstd in
theorem ext_std (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hstd] with v h1 h2
  rw [h1, h2]


include hstd in
theorem rest_ext (f : SInf F (Fin n × Fin d)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ)


include hstd in
theorem acts_ext [DecidableEq T] (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hstd φ)) ?_
  simpa only [ext_of_mem] using h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hvac φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobalPair.Transfer

end

noncomputable section

open scoped Classical


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobalPair.Transfer in
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac mem_of_pure mem_of_tprod) in
theorem GlobalTheory.HoweGlobalPair.tensor_transfer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
    (∀ v, M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) →
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ N, GlobalTheory.SquareAgree.IsThetaSubG M ψ emb om N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) [DecidableEq {v // v ∈ T}]
      (L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))) →ₗ[ℂ] ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobalPair.relInf M ψ emb om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ w : T, ∀ x ∈ GlobalTheory.HoweGlobalPair.relFin om w.1, ∀ (x₀ : ↥(M.Pol ψ emb)) (y : ∀ w' : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y w x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf M ψ emb om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ w : T, ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om w.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) ∈ N) := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb om hvac hstd N hN T _ L hL
  have hLe : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin n × Fin d)) (ext M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem M T φ v h)
  have hpA := pure_mem_algD M T hvac (ψ := ψ) emb
  have hR := rest_ext M T hvac hstd
  have hSB := ext_mem_SB M T hvac
  have hV := ext_vac M T
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD M ψ emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)),
        GlobalTheory.HoweGlobalPair.relInf M ψ emb om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.lie γ hγ f hf _ x.2 hD _ (hSB φ) (hV φ)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe]
        exact hN.cpt k hk _ f.2 _ f₁.2 hA _ (hSB φ) (hV φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro w x hx x₀ y
    rw [hLe]
    refine hN.fin w.1 _ _ x₀.2 (hSB _) (hV _) ?_
    rw [ext_of_mem M T _ w, Function.update_self]
    exact hx
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.stabCpt k hk _ ht
    · let S : Submodule ℂ (↥(M.Pol ψ emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add (f := _), Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.stabLie γ hγ _ ht _ (hLA _) (hS t)
  · intro w g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w' => (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g w') (φ w')) =
          Function.update φ w (g (φ w)) := by
        funext w'
        by_cases hw : w' = w
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext M T hvac hstd _ φ w (g (φ w)) _ (hA (φ w))]
    rw [e]
    exact hN.stabFin w.1 h hh _ ht

end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finitePlace_unitaryPoint_keeps_zeroMatchedData : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (1, h) Φ) := by
  first | exact @GlobalTheory.PolKerFin.polZero_om_fin | exact GlobalTheory.PolKerFin.polZero_om_fin | (intros; apply GlobalTheory.PolKerFin.polZero_om_fin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.finiteIdeleModulus_conjLevelDet_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) = 1 := by
  first | exact @GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | exact GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one | (intros; apply GlobalTheory.DetIdeleUnit.absFin_detAt_conj_eq_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V), infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧ (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧ ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  first | exact @GlobalTheory.TopLevelInv.detAt_cutPart_parts | exact GlobalTheory.TopLevelInv.detAt_cutPart_parts | (intros; apply GlobalTheory.TopLevelInv.detAt_cutPart_parts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.offPlacesPart_movedLevel_keeps_standardHomLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ u : WO (G.pS (.top t (j + 1) : Pair T)) (G.pT (.top t (j + 1) : Pair T)),
      u ∈ stdLatO S (.top t (j + 1)) ↔ ∃ u₀ ∈ stdLatO S (.top t (j + 1)),
        u = actO _ _ (cutPart (1 - (e + cA D e)) (G.V (.top (j + 1)))
          ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))) 1 u₀ := by
  first | exact @GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | exact GlobalTheory.OffPartLattice.offPart_keeps_stdLatO | (intros; apply GlobalTheory.OffPartLattice.offPart_keeps_stdLatO <;> assumption)
end
