module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle421
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle006
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle080
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SixthWeightPurity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle074
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle070
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.HubX
theorem exists_canonical_hubData_with_bounds : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (_root_.GlobalTheory.T.galoisRepsCusp_of_adm2 D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _
end GlobalTheory.HubX
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.commutingEndomorphismCondition_of_serLoc : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D → _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  first | exact @_root_.GlobalTheory.PassOp.main_alt_alt | exact _root_.GlobalTheory.PassOp.main_alt_alt | (intros; apply _root_.GlobalTheory.PassOp.main_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.MuBlock
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
end GlobalTheory.MuBlock
namespace GlobalTheory.MuBlock
end GlobalTheory.MuBlock
namespace GlobalTheory.MuBlock
theorem mu_block_mem_alt : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm3 D → SumRepresentations.adm5 D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    GlobalTheory.RowCopy.RowSize D → GlobalTheory.RowCopy.HeckeSplitOne D →
    ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)),
    D.what₂.isot (D.nd.j i) σ ≠ ⊥ → thetaOf D.nd D.naut i σ P → IsBCV D.nd D.naut i P Pa →
    (⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D hT h3 h5 h7 hRS hH i σ P Pa hσ hth hB
  have hgood : ∀ᶠ w in Filter.cofinite, (∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG (D.naut.muC i) w) := by
    refine Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)
    exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
  obtain ⟨w0, hw0, hs0⟩ := exists_split_not_mem D.nd h5.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : (∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG (D.naut.muC i) w0) := by
    simpa using hw0
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := _root_.GlobalTheory.MuBlock.split_step_o_alt D hT h3 h7 hRS i σ P Pa hσ hth hB w0 hs0 hg0.1 hg0.2
  have hall : ∀ w, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG (D.naut.muC i) w)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    fun w hw hs => (_root_.GlobalTheory.MuBlock.split_step_o_alt D hT h3 h7 hRS i σ P Pa hσ hth hB w hs hw.1 hw.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG (D.naut.muC i) w) →
      D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π, d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π = D.naut.tw (D.naut.muC i) D.naut.etaTinv := by
    refine hH π _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.2)]
  subst hν
  exact hp0
end GlobalTheory.MuBlock
end
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.JumpStatement
theorem holds_all_alt : ∀ D : D7, _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := _root_.GlobalTheory.JumpSets.stmtJ_holds_alt
end GlobalTheory.JumpStatement
end
end

section



section
noncomputable section
namespace GlobalTheory.EigenPoint
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
section Alg
variable {Γ : Type} [Group Γ] {K : Type} [Field K]
end Alg
variable (D : D7) (i : D.nd.Loc)
theorem mem_ZN_alt (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (h2 : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight') (h3 : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation') (h4 : _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition) (h8 : EigenCharTwist)
    (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount) (h11 : Numerics) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (x : D.nd.X i) (v : Fin D.R.nV → Kf D.nd i) (hv0 : v ≠ 0)
    (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    x ∈ ZN D.nd D.naut i := by
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hBC⟩ := hA.1.1.2.2.1 i P
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    (GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)).2.1
  obtain ⟨p, hpL, u, hu0, hu⟩ := h8 (Qbar (D.nd.l i)) (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) D.R.nV
    (mapRep (iotaOQ D.nd D.naut i) (r x)) (twList D i Pa R) (cU D i) hss (_root_.GlobalTheory.EigenPoint.isSSRep_of_mem_twList D i Pa R hR)
    (fun g => (hcp g).trans (twList_cp D i Pa R g).symm) (eig_map D i (r x) v hv0 hv)
  obtain ⟨k, a, ha, rfl⟩ := mem_twList D i hpL
  have hW : ∀ g, ((epsQ D i g)⁻¹ ^ a) • ((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
      (Qbar (D.nd.l i))).mulVec u = iotaOQ D.nd D.naut i (chi1 D.nd i g) • u := fun g => by
    have e := hu g
    rw [twGL_val, Matrix.smul_mulVec, eU_pow] at e
    exact e
  have hwt := h2 D hA i x P Pa hP hBC k (R k) (hR k) a ha ⟨u, hu0, hW⟩
  have hmem : Pa.get k ∈ Pa := List.get_mem Pa k
  have ha1 : 1 ≤ (Pa.get k).a := (hBC.1 _ hmem).1
  have hr1 : 1 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k
    show 1 < D.R.k + D.R.m - 1
    omega
  have ht2 : 2 ≤ D.R.t := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; have := D.R.rank_add_five_le
    omega
  have hle : (Pa.get k).d • Ak k ≤ D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact Multiset.le_add_right _ _
  have hnum := h11 D.R.r D.R.t (Pa.get k).d (Pa.get k).a a (Ak k) hr1 ht2 ha hwt (hAk k).1 (hAk k).2 ha1 hle
  have ha0 : a = 0 := by rw [hnum.2] at hwt; omega
  subst ha0
  have hpart := _root_.GlobalTheory.EigenPoint.eq_one_twist_t_of_mulVec_eigen D i h3 h4 hA hg (Pa.get k) (R k) (hR k) hnum.1 hnum.2 u hu0
    (fun g => by simpa using hW g)
  exact ⟨P, hP, Pa, hBC, hpart ▸ hmem⟩
theorem isCuspIso_of_hasParamX (h1 : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt) (hrc : _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount)
    (h12 : Rest) (hA : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) (hRb : RbEx D) (hg : HG D.nd D.naut i)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (Sig : List (Part D.naut.CG)) (hSig : HasParamX D.nd D.naut i x Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨P, hP, hBC⟩ := hSig
  have hlen : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).length = Sig.length + 1 := by
    simp [twistIso]
  have hlast : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).get
      (Fin.cast hlen.symm (Fin.last _)) = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]
    simp [twistIso, muPart, List.getElem_append_right]
  generalize hPa : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv = Pa at hBC hlen hlast
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  rw [sum_split hlen] at hsum
  have hAl : Ak (Fin.cast hlen.symm (Fin.last _)) = {1} :=
    ms_one ((hAk _).1.trans (by rw [hlast])) (hAk _).2
  have hlt : (Pa.get (Fin.cast hlen.symm (Fin.last _))).d • Ak (Fin.cast hlen.symm (Fin.last _)) =
      Multiset.replicate D.R.t 1 := by
    rw [hAl, hlast]
    exact Multiset.nsmul_singleton _ _
  rw [hlt, ← Multiset.singleton_add] at hsum
  have hS := add_right_cancel hsum
  have hmem : ∀ k : Fin Sig.length, Pa.get (Fin.cast hlen.symm k.castSucc) ∈ Pa := fun k => List.get_mem _ _
  have hG := h12 (Fin Sig.length) (fun k => (Pa.get (Fin.cast hlen.symm k.castSucc)).d)
    (fun k => Ak (Fin.cast hlen.symm k.castSucc)) D.R.r (fun k => (hBC.1 _ (hmem k)).2.1)
    (fun k h => by
      have e := (hAk (Fin.cast hlen.symm k.castSucc)).1
      rw [h, Multiset.sum_zero] at e
      have := (hBC.1 _ (hmem k)).1
      omega) hS
  have hl1 : Sig.length = 1 := by simpa using hG.1
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl1
  have h0 := hG.2 ⟨0, by simp⟩
  have hget : Pa.get (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length))) =
      ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ := by
    subst hPa
    simp [twistIso]
  have hd : p.d = 1 := by have := h0.1; rw [hget] at this; exact this
  have ha : p.a = D.R.r := by
    have e := (hAk (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length)))).1
    rw [h0.2, hget, Multiset.sum_singleton] at e
    exact e.symm
  rcases p with ⟨a, π, d⟩
  dsimp only at hd ha
  subst hd ha
  exact ⟨π, rfl⟩
theorem prvG6_of_realisation_mu_res_count_numerics : _root_.GlobalTheory.StringRepresentationDecomposition.CentredStringDecompositionAlt → _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' → _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' → _root_.GlobalTheory.StringRepresentationDecomposition.MuCharacterCondition → EigenCharTwist → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount → Numerics → Rest →
    ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D → RbEx D → SumRepresentations.ConclusionG6 D :=
  fun h1 h2 h3 h4 h8 hrc h11 h12 D hA hRb i hg r hr x hx =>
    ⟨hx.elim fun v hv => _root_.GlobalTheory.EigenPoint.mem_ZN_alt D i h1 h2 h3 h4 h8 hrc h11 hA hRb hg r hr x v hv.1 hv.2,
      fun Sig hSig => _root_.GlobalTheory.EigenPoint.isCuspIso_of_hasParamX D i h1 hrc h12 hA hRb hg r hr x Sig hSig⟩
end GlobalTheory.EigenPoint
end
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.resCount_of_valRing_ssList_ssRank : ValRingModel → SSList → SSRankUnique → _root_.GlobalTheory.StringRepresentationDecomposition.ResidueCount := by
  first | exact @_root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | exact _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt | (intros; apply _root_.GlobalTheory.ResidualRankCount.residual_count_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.hecke_char_eq_of_l_adic_realisation : _root_.GlobalTheory.StringRepresentationDecomposition.HeckeCharEqOfLAdicRealisation' := by
  first | exact @_root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | exact _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt | (intros; apply _root_.GlobalTheory.HeckeCharacterEquality.sixth_character_equality_holds_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.purity_string_weight : _root_.GlobalTheory.StringRepresentationDecomposition.PurityStringWeight' := by
  first | exact @_root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | exact _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt | (intros; apply _root_.GlobalTheory.FrobeniusCharacterNorms.sixth_weight_purity_alt_alt <;> assumption)
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
abbrev _root_.GlobalTheory.Pass.stepType_proof_tyz : Prop :=  _root_.GlobalTheory.Pass.StepTypeAlt
end
end

section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.Pass.ResidualSpan
theorem main_alt_alt : _root_.GlobalTheory.Pass.ResidueStatement := by
  intro D hRb _ i r ρ hr π hπ hd
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have h := hRb.2 i hHG _ hrb
  unfold ResSpan
  convert h using 3
  funext g
  first
    | rfl
    | (ext a b; simp [mapM, rhoO, redRep, mapRep])
end GlobalTheory.Pass.ResidualSpan
end
end

section



section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
open GlobalTheory.MuCharProof
noncomputable section
namespace UpperTheory.GalS
open UpperTheory.Lit.Car
theorem muChar_holds_alt : _root_.GlobalTheory.MuCharProof.muChar_holds_tyz := by
  intro D hA i hg ρ hρ w hw
  obtain ⟨x, ⟨P, -, Pa, hBC, hmem⟩, -⟩ := hg
  have h2 := _root_.UpperTheory.GalS.weak' hA.1.1.2.2.2.1
  have h5 : Formalism.MainNotions.SumRepresentations.adm5 D := hA.1.1.2.2.2.2.2.2
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχ
  set s : ℝ := ((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2 with hs
  have halg : ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ) := by
    intro τ z hz
    have ht : 0 ∈ List.range D.R.t := List.mem_range.2 D.R.t_odd.pos
    have h1 : z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ isoInf D.nd D.naut Pa τ := by
      refine mem_list_sum Pa _ hmem ?_
      refine mem_list_sum _ _ (a := ((0 : ℕ) : ℂ)) ?_ ?_
      · simp only [List.mem_range]
        simp
        exact ⟨0, D.R.t_odd.pos, by simp⟩
      · exact Multiset.mem_map_of_mem _ hz
    rw [hBC.2.2.2.2.2 τ] at h1
    let τ' : D.host.E →+* Qbar (D.nd.l i) := (D.naut.iotaQC i).symm.toRingHom.comp τ
    have hτ : (D.naut.iotaQC i).toRingHom.comp τ' = τ := by
      ext e
      simp [τ']
    have hj := D.naut.locAut_hodgeTateWeightsLevelZero_def i τ'
    rw [hτ] at hj
    have h3 : -(z + (((D.R.t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) + ((D.R.nV : ℂ) - 1) / 2 ∈
        (D.naut.locAutHodgeTateWeightsLevelZero i τ').map (fun n : ℤ => (n : ℂ)) := by
      rw [hj]
      exact Multiset.mem_map_of_mem _ h1
    obtain ⟨n, -, hn⟩ := Multiset.mem_map.1 h3
    refine ⟨-n, ?_⟩
    rw [hs]
    push_cast at hn ⊢
    linear_combination hn
  obtain ⟨ρ', hc', hw', -⟩ := (h2 i).2.2 χ s halg
  have hc0 : Continuous fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    have : (fun g => ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0) =
        fun g => iotaOQ D.nd D.naut i (chi1 D.nd i g) := funext hρ
    rw [this]
    exact (Formalism.MainNotions.SumRepresentations.continuous_iotaOQ D.nd D.naut i).comp (D.nd.chi_cont i 1)
  have hc0' : Continuous fun g => ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    hc'.matrix_elem 0 0
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) : Set (PlE D.host)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet
  have hdense := h5.2.2.1 _ hfin
  have hsub : {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ (placesOver D.host.E (D.nd.l i) ∪ ↑(D.nd.S i) ∪ ↑(D.nd.Q i) :
      Set (PlE D.host)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} ⊆
      {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := by
    rintro σ ⟨v, hv, hsp, B, hB, hσ⟩
    simp only [Set.mem_union, not_or, Finset.mem_coe] at hv
    have hso : SplitOut D.nd i v := ⟨hsp, hv.1.1, hv.1.2, hv.2⟩
    obtain ⟨hu, hf⟩ := D.naut.chi_mu i v hso
    have hunr : D.naut.unr (D.naut.wdOf i ρ' v) := by
      rw [hw' v hv.1.1]
      exact (D.naut.unr_tw _ _).2 hu
    have e := D.naut.wdOf_frob i ρ' v hv.1.1 hc' hunr B σ hB hσ
    rw [hw' v hv.1.1, hf B σ hB hσ, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
    have e2 := (D.naut.iotaQC i).injective (C_injective (sub_right_injective e))
    show _ = _
    rw [hρ σ]
    exact e2.symm
  have hall : ∀ g, ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := by
    intro g
    have hcl : IsClosed {g | ((ρ g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
        ((ρ' g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0} := isClosed_eq hc0 hc0'
    have := closure_minimal hsub hcl
    rw [hdense] at this
    exact this (Set.mem_univ g)
  have heq : ρ = ρ' := by
    refine MonoidHom.ext fun g => Units.ext (Matrix.ext fun a b => ?_)
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    exact hall g
  rw [heq]
  exact hw' w hw
end UpperTheory.GalS
end
end
end
