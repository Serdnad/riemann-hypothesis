module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle161
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle074
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
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
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

theorem exists_tieIn_reCore : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → FrameKs T.Q.c.F R.MW → ∃ dict mu chiW x₀, TieIn (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) ∧ LawsCore (reCore T dict mu chiW x₀ T.cE).toCore := by
  intro D G _ _ Pl0 T0 A T _ R hvol hJ hC ha hlev hval hfr
  obtain ⟨chiW, hchi, hchi'⟩ := GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings D G Pl0 T0 A T R hJ.pins ha hlev hval
  obtain ⟨x₀, hx, hx'⟩ := GlobalTheory.T.exists_orthonormal_baseFrames_flag_domain_models D G Pl0 T0 A T R hJ ha hfr
  obtain ⟨mu, hJ1, hC1⟩ := GlobalTheory.T.exists_core_laws_for_replaced_hecke_characters D T chiW hJ hC hchi'
  obtain ⟨dict, hJ2, hC2⟩ := GlobalTheory.T.exists_dictionary_core_laws_baseFrame_change D (reCore T T.dict mu chiW T.x₀ T.cE) x₀ hvol hJ1 hC1 hx'
  exact ⟨dict, mu, chiW, x₀, tieIn_top (reCore T dict mu chiW x₀ T.cE) R hJ2 ha
    (GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets D G Pl0 T0 A T.Q.c.F R) hchi hx, hC2⟩

end GlobalTheory.RealGeo
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficientField_form_value_mem_polynomialModel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  first | exact @GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | exact GlobalTheory.Mem.KerVal.fm_succ_mem_valQ | (intros; apply GlobalTheory.Mem.KerVal.fm_succ_mem_valQ <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_coefficientField_form_of_polynomialModel_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  first | exact @GlobalTheory.Mem.Col2.TC.form_of_rat_values | exact GlobalTheory.Mem.Col2.TC.form_of_rat_values | (intros; apply GlobalTheory.Mem.Col2.TC.form_of_rat_values <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.exists_rows_prescribedUnitaryForms_standIns : ∀ (B : Base) (C : Cols B) (n : C.Tup → ℕ) (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n C.mu0))) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (n a))) (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (EuclideanSpace ℂ (Fin (n a)))) (mt : B.places.Pl → C.Tup), (∀ w, mt (B.places.conj w) = mt w) → SpectralModel.ColsPos C → ∃ (W : RowsRest B C) (g : ∀ a, EuclideanSpace ℂ (Fin (n a)) ≃ₗᵢ[ℂ] W.Amb a), StandIn W ∧ (∀ w, W.muAt w = C.mu0) ∧ (∀ w, W.muTw w = mt w) ∧ (∀ u F, W.eMt0 u F = g C.mu0 (e0 u F)) ∧ (∀ u a F, W.eMtTw u a F = g a (eT u a F)) ∧ (∀ a y, g a y ∈ (W.Mtilde a).carrier ↔ y ∈ (L a).carrier) ∧ (∀ a y, g a y ∈ (W.Mtilde a).gen ↔ y ∈ (L a).gen) ∧ (∀ a, W.eOp a = LinearMap.id) ∧ ∀ u a, W.ze u a = 1 := by
  first | exact @GlobalTheory.Mem.DfGen.exists_rowsRest_std | exact GlobalTheory.Mem.DfGen.exists_rowsRest_std | (intros; apply GlobalTheory.Mem.DfGen.exists_rowsRest_std <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.KerEntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1


open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in
theorem adaptedTh_kerEntC {D : D7} {P : Examples₂.EntPl D} {O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)} {Bs : PlaceMatrixFamily D} {Dx : DivX D} {Tw : TwForms D}
    (hB : BasOk P O Bs) (hA : AdaptedEnt P O Bs Dx) (h : KerEntHyp P O Bs Dx Tw) : AdaptedTh (kerEntC P O Bs h) O := by
  intro w hw u μ hl
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hA w hw u μ hl
  refine ⟨Pm, h1, h2, h3, fun i hi c c' => ?_⟩
  show thAtW P O Bs u μ w i c c' = _
  unfold thAtW
  congr 1
  funext k j
  unfold adCoef
  split_ifs with hk
  · set s := Formalism.MainNotions.TaylorLogMetric.lamC (P.lam w) ((O u μ).dgen k.1) with hs
    have hs0 : s ≠ 0 := by
      intro h0
      have hd := (hB u μ w (i + 1) hi c' k.1).1
      haveI hne : Nonempty (Fin (D.R.N (i + 1))) := ⟨j.2.2⟩
      rw [h4 (i + 1) hi c' k.1, ← hs, h0, _root_.inv_zero, zero_pow (by omega), zero_smul] at hd
      exact hd Matrix.det_zero
    have hdet : ((Pm i c k.1).map (tauEmb D (P.lam w) k.1)).det ≠ 0 := (h1 i hi.le c k.1).1
    have ht : s⁻¹ ^ i ≠ 0 := pow_ne_zero _ (inv_ne_zero hs0)
    have hinv : (s⁻¹ ^ i • (Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ =
        (s⁻¹ ^ i)⁻¹ • ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [h4 (i + 1) hi c' k.1, h4 i hi.le c k.1, ← hs, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : (1 : ℂ_[D.what₂.places.resChar w]) * s * s⁻¹ ^ (i + 1) * (s⁻¹ ^ i)⁻¹ = 1 := by
      rw [inv_pow, inv_pow, inv_inv, pow_succ]
      field_simp
    simp only [show (kerEntC P O Bs h).lam w = P.lam w from rfl]
    generalize ((Pm (i + 1) c' k.1).map (tauEmb D (P.lam w) k.1)) k.2.1 j.2.2 = x
    generalize ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ j.2.1 k.2.2 = y
    linear_combination (x * y) * e
  · rfl

end GlobalTheory.Mem.Col2.KerEntTrue

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem ss_exists : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := GlobalTheory.T.exists_semisimplification_matrix_rep_same_charpoly

theorem indep : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := GlobalTheory.T.charpoly_coeff_congr_same_place_alt

theorem ssRep_spec {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep (ssRep ρ) ∧ ρ.ker ≤ (ssRep ρ).ker ∧
    ∀ g, (ssRep ρ g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  Classical.epsilon_spec (ss_exists ρ)

theorem castMt_eq {D : D7} {μ μ' : D.what₂.Tup} {j j' : ℕ} (h1 : μ = μ') (h2 : j = j') (M : Submodule ℂ (D.what₂.Mt μ j))
    (M' : Submodule ℂ (D.what₂.Mt μ' j')) (h : HEq M M') : castMt h1 h2 M = M' := by
  subst h1; subst h2; exact eq_of_heq h

theorem isOpen_ker_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {O : Type} [CommRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (I : Ideal O) (hI : IsOpen (I : Set O)) {k : Type} [CommRing k] (φ : O →+* k)
    (hφ : I ≤ RingHom.ker φ) {a : ℕ} (ρ : Γ →* GL (Fin a) O)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin a) (Fin a) O)) :
    IsOpen ((mapRep φ ρ).ker : Set Γ) := by
  let U : Set Γ := ⋂ i : Fin a, ⋂ j : Fin a, (fun g => (ρ g : Matrix (Fin a) (Fin a) O) i j - (1 : Matrix (Fin a) (Fin a) O) i j) ⁻¹' (I : Set O)
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hI.preimage ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp hρ)).sub continuous_const
  have h1 : (1 : Γ) ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_preimage, map_one, Units.val_one, sub_self]
    intro i j; exact I.zero_mem
  have hsub : U ⊆ ((mapRep φ ρ).ker : Set Γ) := by
    intro g hg
    simp only [U, Set.mem_iInter, Set.mem_preimage] at hg
    show mapRep φ ρ g = 1
    apply Units.ext
    ext i j
    have := hφ (hg i j)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
    simp only [mapRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Units.val_one]
    change φ ((ρ g : Matrix (Fin a) (Fin a) O) i j) = (1 : Matrix (Fin a) (Fin a) k) i j
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1) hsub)

theorem isSSRep_one {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} : IsSSRep (1 : Γ →* GL (Fin a) k) := by
  intro W _
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
  exact ⟨W', fun g v hv => by simpa using hv, hW'⟩

theorem fbCast_trans {p q r : ℕ} (h1 : p = q) (h2 : q = r) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (x : Fb p hp) :
    fbCast h2 hq hr (fbCast h1 hp hq x) = fbCast (h1.trans h2) hp hr x := by
  subst h1; subst h2; rfl

theorem plκ_cast (D : D7) (Pl : PlSide D) {lam lam' : D.what₂.places.Pl} (h : lam = lam') {p : ℕ} (hp : p.Prime)
    (h1 : D.what₂.places.resChar lam = p) (h1' : D.what₂.places.resChar lam' = p) (z z' : ℂ) (hz : z ∈ Pl.plB lam)
    (hz' : z' ∈ Pl.plB lam') (hd : z - z' ∈ (Pl.plB lam).nonunits) :
    fbCast h1 (D.what₂.places.resChar_prime lam) hp (Pl.plκ lam (IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩)) =
      fbCast h1' (D.what₂.places.resChar_prime lam') hp (Pl.plκ lam' (IsLocalRing.residue (Pl.plB lam') ⟨z', hz'⟩)) := by
  subst h
  have : IsLocalRing.residue (Pl.plB lam) ⟨z, hz⟩ = IsLocalRing.residue (Pl.plB lam) ⟨z', hz'⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [ValuationSubring.mem_nonunits_iff] at hd
    simpa using hd
  rw [this]

theorem charpoly_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B).charpoly = (ρ g : Matrix (Fin a) (Fin a) A).charpoly.map f := by
  rw [← Matrix.charpoly_map]
  rfl

theorem isSSRep_rbarOf {D : D7} {X : LocNd (lay0 D)} (Y : LocAut X) (σ : D.what₂.FT) (lam : D.what₂.places.Pl) :
    IsSSRep (rbarOf Y σ lam) := by
  unfold rbarOf
  split_ifs with h
  · exact (ssRep_spec _).1
  · exact isSSRep_one


theorem rbar_tie_at (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X)
    (hCheb : GlobalTheory.RowTie.ChebSplit D.nd) (hloc : ∀ i σ w, Y.locW i σ w = Rw.locR σ w)
    (hplB : ∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y))
    (i : X.nd.Loc) (σ : D.what₂.FT) (Sig : List (Formalism.BasicNotions.Part Y.naut.CG))
    (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (hP : HasParamW X.nd Y.naut i σ Sig)
    (hR : IsRepOfSig X.nd Y.naut i Sig ρ) (g : G D.host.E X.nd.Om) :
    ((rbarOf Y σ (X.nd.w i) g : Matrix (Fin D.R.r) (Fin D.R.r) _).charpoly).map
        (fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out).toRingHom =
      (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.map ((Y.naut.kFbar i).comp (IsLocalRing.residue (X.nd.O i))) := by
  have hex : RbarData Y σ (X.nd.w i) := ⟨i, rfl, Sig, ρ, hP, hR⟩
  unfold rbarOf
  rw [dite_eq_left hex, (ssRep_spec _).2.2 g, charpoly_mapRep, Polynomial.map_map]
  have hw0 := hex.choose_spec.1
  have hs := hex.choose_spec.2.choose_spec.choose_spec
  generalize hex.choose_spec.2.choose_spec.choose = ρ0 at hs ⊢
  generalize hex.choose_spec.2.choose = Sig0 at hs ρ0 ⊢
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  obtain ⟨hz0, e0⟩ := hplB hex.choose ((ρ0 g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O hex.choose)).charpoly.coeff n)
  obtain ⟨hz, e⟩ := hplB i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n)
  rw [← e0, ← e, fbCast_trans, fbCast_trans]
  exact plκ_cast D Pl hw0 _ _ _ _ _ hz0 hz
    (indep D Rw Pl X Y hCheb hloc hplB σ _ i hw0 Sig0 Sig ρ0 ρ hs.1 hs.2 hP hR g n)



theorem locTy_exists : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), BlocksUnique D → GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ i : X.nd.Loc, Y.naut.iotaQC i = qCast (X.nd.w_l i) (Pl.ι (X.nd.w i))) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → (∀ i k v, X.nd.gam0 i (D.naut.plGw k v) = D.ntypes.tg k v) → (∀ (i : X.nd.Loc) k v, X.nd.l i ≠ D.host.g k → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; ∃ u : (ZMod (D.host.g k))ˣ, (u = D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩ ∨ u = (D.nd.chiT k v ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩)⁻¹) ∧ iotaO X.nd Y.naut i ((X.nd.chi i 1 (D.ntypes.tg k v) : (X.nd.O i)ˣ) : X.nd.O i) = D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)))) → (∀ (i i' : X.nd.Loc) (σ' : (lay0 D).ntypes.Par), X.nd.mu i = X.nd.mu i' → X.nd.j i = X.nd.j i' → HEq (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i]) Y.naut.etaTinv)}, Y.naut.typeV i P) (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc X.nd Y.naut Sig w = (lay0 D).ntypes.locPar σ' w) ∧ IsBCV X.nd Y.naut i' P (twistIso X.nd Y.naut (Sig ++ [muPart X.nd Y.naut i']) Y.naut.etaTinv)}, Y.naut.typeV i' P)) → ∃ Z : LocTy Y, BcTie X.nd Y.naut Z.ntypes ∧ RbarTie X.nd Y.naut Z.ntypes ∧ MtParTie X.nd Y.naut Z.ntypes ∧ ∀ σ lam, IsSSRep (Z.rbar σ lam) := by
  intro D Rw Pl X Y hBU hCheb hloc hiota hplB hgam hchi hMt
  refine ⟨{ bc := bcOf D Rw, bc_pos := ?_, bc_sum := ?_, rbar := rbarOf Y, rbar_open := ?_, heckeLoc_gamma_places := hgam, chiT_tg := ?_, MtPar := mtParOf Y }, ?_, ?_, ?_, ?_⟩
  · intro σ p hp
    unfold bcOf at hp
    split_ifs at hp with h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hp)
      obtain ⟨h1, h2, -⟩ := h.choose_spec.1 q hq
      exact ⟨h1, h2⟩
    · rw [Multiset.mem_singleton] at hp; subst hp
      refine ⟨?_, Nat.one_pos⟩
      have := D.R.m_add_three_le_k; have := D.R.two_le_m
      simp only [Ranks.r]; omega
  · intro σ
    unfold bcOf
    split_ifs with h
    · have := h.choose_spec.2.1
      simp only [Multiset.map_coe, Multiset.sum_coe, List.map_map]
      simpa [rankIso, Function.comp_def] using this
    · simp
  · intro σ lam
    show IsOpen (((rbarOf Y σ lam).ker : Subgroup _) : Set (G D.host.E X.nd.Om))
    unfold rbarOf
    split_ifs with h
    · apply Subgroup.isOpen_mono (ssRep_spec _).2.1
      have hc := h.choose_spec.2.choose_spec.choose_spec.2.1
      refine isOpen_ker_mapRep (IsLocalRing.maximalIdeal (X.nd.O h.choose)) ?_ _ ?_ _ hc
      · have := (isAdic_iff.1 (X.nd.O_adic h.choose)).1 1
        simpa using this
      · intro y hy
        rw [RingHom.mem_ker]
        simp [(IsLocalRing.residue_eq_zero_iff y).2 hy]
    · simp [MonoidHom.ker_one]
  · intro i k v hk
    obtain ⟨u, hu, he⟩ := hchi i k v hk
    rcases hu with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · intro i σ Sig hP hcsd hinf
    have hg : BcGood D Rw σ Sig := ⟨fun p hp => ⟨(hP.1 p hp).1, (hP.1 p hp).2, hcsd p hp, hinf p hp⟩, hP.2.1,
      fun w hw => (hP.2.2 w hw).trans (hloc i σ w)⟩
    have hex : ∃ Sig, BcGood D Rw σ Sig := ⟨Sig, hg⟩
    show bcOf D Rw σ = _
    unfold bcOf
    rw [dite_eq_left hex]
    have h0 := hex.choose_spec
    refine hBU _ _ (fun p hp => ?_) h0.2.1 hg.2.1 (fun w hw => (h0.2.2 w hw).trans (hg.2.2 w hw).symm)
    rcases List.mem_append.1 hp with hp | hp
    · exact h0.1 p hp
    · exact hg.1 p hp
  · intro i σ Sig ρ hP hR
    refine ⟨?_, rbar_tie_at D Rw Pl X Y hCheb hloc hplB i σ Sig ρ hP hR⟩
    exact isSSRep_rbarOf Y σ (X.nd.w i)
  · intro i σ'
    show mtParOf Y (X.nd.mu i) (X.nd.j i) σ' = mtSup Y i σ'
    have hex : ∃ i', X.nd.mu i' = X.nd.mu i ∧ X.nd.j i' = X.nd.j i := ⟨i, rfl, rfl⟩
    unfold mtParOf
    rw [dite_eq_left hex]
    exact castMt_eq _ _ _ _ (hMt _ _ σ' hex.choose_spec.1 hex.choose_spec.2)
  · exact fun σ lam => isSSRep_rbarOf Y σ lam

end GlobalTheory.HeightCounting

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.chartLevelFunctionals_intermediateSteps_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  first | exact @GlobalTheory.Mem.Col2.TC.fvTie_charts | exact GlobalTheory.Mem.Col2.TC.fvTie_charts | (intros; apply GlobalTheory.Mem.Col2.TC.fvTie_charts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelFunctional_chart_lastStep_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  first | exact @GlobalTheory.Mem.Col2.TC.fvTie_chart_top | exact GlobalTheory.Mem.Col2.TC.fvTie_chart_top | (intros; apply GlobalTheory.Mem.Col2.TC.fvTie_chart_top <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.host_primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.primes_over_level_place | exact GlobalTheory.Mem.Col2.HAt.primes_over_level_place | (intros; apply GlobalTheory.Mem.Col2.HAt.primes_over_level_place <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.exists_tupleUnitaryForms_equiv_periodRowForms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok), ∀ (u : B.Word) (a : I.ι), ∃ g : MtCx I a ≃ₗ[ℂ] (I.per l u a).Mt, ∀ F, SameForm I l u a F (g F) := by
  first | exact @GlobalTheory.Mem.Df.mtCx_equiv_per | exact GlobalTheory.Mem.Df.mtCx_equiv_per | (intros; apply GlobalTheory.Mem.Df.mtCx_equiv_per <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.integralFormsHermLattice_good_and_complexBasis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  first | exact @GlobalTheory.Mem.Df.mtHL_good_basis | exact GlobalTheory.Mem.Df.mtHL_good_basis | (intros; apply GlobalTheory.Mem.Df.mtHL_good_basis <;> assumption)
end
