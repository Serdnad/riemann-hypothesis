module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle205
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KernelRationalReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle195
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Bundle001
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isMatrixModPlaceInFamily_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_inv | exact GlobalTheory.Mem.SymFrame.isMatIn_inv | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_inv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

def castQ {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) : Qbar p ≃+* Qbar q := by
  subst h; exact RingEquiv.refl _

theorem exists_heq {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) : ∃ z' : ℤ_[q], HEq z z' := by
  subst h; exact ⟨z, HEq.rfl⟩

theorem castQ_alg {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (z : ℤ_[p]) (z' : ℤ_[q]) (hz : HEq z z') :
    (castQ h).symm (algebraMap ℚ_[q] (Qbar q) (z' : ℚ_[q])) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := by
  subst h
  obtain rfl := eq_of_heq hz
  rfl

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {n : ℕ} (f : A →+* B)
    (g : B →+* C) (ρ : Γ →* GL (Fin n) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  rfl

theorem isRepOf_cast (D : D7) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (ι : Qbar q ≃+* ℂ) {n : ℕ}
    (π : D.naut.CG n) (s : ℝ) (ρ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar q))
    (hρ : IsRepOf D p ((castQ h).trans ι) π s (mapRep (castQ h).symm.toRingHom ρ)) : IsRepOf D q ι π s ρ := by
  subst h
  have e1 : (castQ (rfl : p = p)).trans ι = ι := by ext x; rfl
  have e2 : mapRep (castQ (rfl : p = p)).symm.toRingHom ρ = ρ := by ext g i j; rfl
  rw [e1, e2] at hρ
  exact hρ

theorem conj_of_isRepOf (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (π : D.naut.CG n) (s : ℝ)
    (hC : GlobalTheory.RowTie.ChebSplit D.nd) (ρ₁ ρ₂ : G D.host.E D.nd.Om →* GL (Fin n) (Qbar l))
    (h₁ : IsRepOf D l ι π s ρ₁) (h₂ : IsRepOf D l ι π s ρ₂) : IsConjRep ρ₁ ρ₂ := by
  obtain ⟨c₁, s₁, f₁⟩ := h₁
  obtain ⟨c₂, s₂, f₂⟩ := h₂
  have hfin := (Filter.eventually_cofinite.mp f₁).union (Filter.eventually_cofinite.mp f₂)
  have hcp := GlobalTheory.TwistLG.charpoly_eq_of_dense ρ₁ ρ₂ c₁ c₂ _ (hC hfin.toFinset).closure_eq (by
    rintro g ⟨w, hw, -, B, hB, hg⟩
    rw [Set.Finite.mem_toFinset] at hw
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [hw.1 B g hB hg, hw.2 B g hB hg])
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₂ ρ₁ s₂ s₁ (fun g => (hcp g).symm)
  exact ⟨P⁻¹, fun g => by rw [hP g, inv_inv]⟩

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) : M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Matrix.charmatrix_apply_eq]
  rfl

theorem rhoOfRow_isRepOf (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    IsRepOf D (D.nd.l a) (D.naut.iotaQC a) (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
      (rhoOfRow D hG hC hη a π hc hr) := by
  obtain ⟨c1, ss1, f1⟩ := rowRho_spec D hG a π hc hr
  obtain ⟨cχ, awayχ, -⟩ := Classical.choose_spec (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη)
  set χ1 := Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη) with hχ1
  have e0 : rhoOfRow D hG hC hη a π hc hr =
      Formalism.MainNotions.SumRepresentations.At.twGL (rowRho D hG a π hc hr) (Matrix.GeneralLinearGroup.det.comp χ1) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; exact GlobalTheory.TwistLG.cont_twGL _ _ c1 cχ
  · rw [e0]; exact GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1
  have hfin := placesOver_finite D.host.E (D.nd.l a) (Fact.out : (D.nd.l a).Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : w ∉ placesOver D.host.E (D.nd.l a) := hwl

  have hue : D.naut.unr (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) :=
    (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  obtain ⟨u, hu1⟩ : ∃ u, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    apply Multiset.card_eq_one.mp
    rw [D.naut.frobEig_tw _ _ (D.naut.etaTinv_def w).1, Multiset.card_map,
      D.naut.frobEig_card _ (D.naut.etaTinv_def w).1, D.naut.locG_dim]
  have hwd := D.naut.wdOf_frob a χ1 w hwl' cχ (by rw [awayχ w hwl']; exact hue) B σ hB hσ
  rw [awayχ w hwl', hu1, Multiset.map_singleton, Multiset.prod_singleton, charpoly_fin_one, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C] at hwd
  have hχu : D.naut.iotaQC a ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) : Qbar (D.nd.l a)) = u := by
    have := congrArg (fun p : Polynomial ℂ => p.coeff 0) hwd
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, neg_inj] at this
    show D.naut.iotaQC a ((χ1 σ : Matrix (Fin 1) (Fin 1) _).det) = u
    rw [Matrix.det_unique]
    exact this

  have h1 := hw1 B σ hB hσ
  rw [isoLoc_single] at h1
  rw [e0, GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((rowRho D hG a π hc hr) σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map
      (D.naut.iotaQC a).toRingHom).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : (D.naut.iotaQC a).toRingHom ((Matrix.GeneralLinearGroup.det.comp χ1 σ : (Qbar (D.nd.l a))ˣ) :
      Qbar (D.nd.l a)) = u := hχu
  rw [hχu']
  exact h3

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR

theorem fracMap_eq {O0 O : Type} [CommRing O0] [IsDomain O0] [ValuationRing O0] [CommRing O] [IsDomain O]
    (f : O0 →+* O) (hf : Function.Injective f) {F : Type} [Field F] (e : F →+* FractionRing O0)
    (e' : F →+* FractionRing O) (h : ∀ x y, algebraMap O0 _ y = e x → e' x = algebraMap O _ (f y)) (x : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap f hf (e x) = e' x := by
  rcases ValuationRing.isInteger_or_isInteger O0 (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [← hy, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, h x y hy]
  · have hy' : algebraMap O0 (FractionRing O0) y = e x⁻¹ := by rw [map_inv₀]; exact hy
    have h1 := h x⁻¹ y hy'
    have h2 : e x = (algebraMap O0 (FractionRing O0) y)⁻¹ := by rw [hy, inv_inv]
    rw [h2, map_inv₀, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg, ← h1, map_inv₀, inv_inv]

end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting.FitRho

open Formalism.L2.NR


end GlobalTheory.HeightCounting.FitRho

namespace GlobalTheory.HeightCounting


end GlobalTheory.HeightCounting
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.QuotVol

theorem quot_volume_ne_zero_ne_top : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    IsQuot V μ 𝓕 → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ := fun D V μ 𝓕 h =>
  ⟨((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram μ h.1).2
      𝓕 𝓕 h.2 h.2).2,
    (GlobalTheory.Mem.VolFin.finVol D.host.F D.host.E D.sp.cm.sig (GlobalTheory.Mem.VolExists.isCMExt D.sp.cm) V.rank V.gram
      (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) μ h.1 𝓕 h.2).ne⟩

end GlobalTheory.Mem.QuotVol
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conjugate_reference_characters_good_embeddings : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), T.Q.Pins → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → ∃ (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ChiAt R i σ (chiW ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ) := by
  first | exact @GlobalTheory.ConjRefChar.exists_chiAt | exact GlobalTheory.ConjRefChar.exists_chiAt | (intros; apply GlobalTheory.ConjRefChar.exists_chiAt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem form_of_rat_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls (i + 1) → ((I.rec7 l Z).chTw u μ).Y (i + 1) → ℂ, φ ∈ ((I.tw l l0 Z).fm u μ).Fi (i + 1) → (∀ c', ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = φ c') → ∃ x, ((I.tw l l0 Z).fm u μ).emb (i + 1) x = φ := by
  intro B X I _hOk _hPins l Z l0 Y O Pl Bs _hQp hStd _hBas _hBsLL _hUnf _hJets u μ i hi φ hφ hv
  have hlam : lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) = lamT (B.hcW u) (i + 1) := by
    funext τ
    show Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (((i+1) * (B.R.t + 1) / 2 : ℕ) : ℤ) =
      GlobalTheory.Mem.Col2.shW (Examples₂.lamOf (B.hcW u τ) (i+1)) (-(((i+1 : ℕ) : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
    obtain ⟨k, hk⟩ := B.R.t_odd
    have e1 : (B.R.t + 1) / 2 = k + 1 := by omega
    have e2 : (i+1) * (B.R.t + 1) / 2 = (i+1) * (k + 1) := by
      rw [show B.R.t + 1 = (k + 1) * 2 by omega, ← mul_assoc, Nat.mul_div_cancel _ two_pos]
    unfold Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
    congr 1
    funext j
    rw [e1, e2, Nat.cast_mul, sub_eq_add_neg]
  obtain ⟨nn, h1, -, h3, h4⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  change ∀ τ r, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).natW r = _ at h3
  change ∀ τ, (lamTG (D := I.rec7 l Z) (I.fm l u μ) (i + 1) τ).detShift = _ at h4
  rw [hlam] at h3 h4
  have hnat : (fun τ r => (lamT (B.hcW u) (i + 1) τ).natW r) = extNu (B.R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
    funext τ r
    refine (h3 τ r).trans ?_
    congr 1
    funext τ' r'
    exact h1 τ' r'
  haveI hLL : Infinite B.LL := Infinite.of_injective (fun n : ℕ => (n : B.LL)) (fun a b h => by
    have := congrArg B.embLL h; simp only [map_natCast] at this; exact_mod_cast this)
  have hVV : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)) = polV (I.rec7 l Z) u (i + 1) := by
    rw [GlobalTheory.PdvKm.VV_eq_WtPol, hnat]; rfl
  have key : ∀ c', ∃ z : Formalism.L2.DIV.VV B.LL (lamT (B.hcW u) (i + 1)),
      evV B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL z = φ c' := by
    intro c'
    obtain ⟨v', hv'⟩ := hv c'
    obtain ⟨⟨Q, hQ⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ v'
    refine ⟨⟨Q, hVV ▸ hQ⟩, ?_⟩
    rw [← hv']
    clear hnat h3 h1 hlam hφ hv hv'
    show _ = evP O u μ (i + 1) ⟨Q, hQ⟩
    funext y
    rw [evV_apply]
    show _ = (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(twB (I.rec7 l Z) u μ (i + 1) τ))) *
      GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL Q) ((O u μ).frm (i + 1) y)
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de (i + 1) y τ = (y.1 τ).det := fun τ => by
      rw [(O u μ).frm_de (i + 1) hi y τ, hStd.frm u μ (i + 1) y]
      rfl
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_mul, shiftOf, twB, GL3Theta.evFr, hStd.frm u μ (i + 1) y, hde, Pi.one_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact congrArg (fun e : ℤ => (y.1 τ).det ^ e) (h4 τ)
  choose z hz using key
  let o : Frames (gramC (1 : Matrix (Fin (B.R.N (i + 1))) (Fin (B.R.N (i + 1))) B.fields.E) (embAt B.embLL B.fields.emb)) :=
    ⟨fun _ => 1, fun τ => by simp⟩
  have hinv : ∀ c' (g : (I.stp u μ (i + 1)).Stab c'),
      (I.stp u μ (i + 1)).rho B.fields.emb (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c') = z c' := by
    intro c' g
    apply evV_injective B.fields.emb 1 (lamT (B.hcW u) (i + 1)) B.embLL o
    have e1 := Law.evV_rho (I.stp u μ (i + 1)) B.fields.emb B.embLL (lamT (B.hcW u) (i + 1)) c'.1 g.1 (z c')
    have e2 := (hφ c').2 g
    refine e1.trans ?_
    refine (congrArg ((I.stp u μ (i + 1)).tr B.fields.emb B.embLL c'.1 g.1) (hz c')).trans ?_
    exact e2.trans (hz c').symm
  refine ⟨⟨z, hinv⟩, ?_⟩
  funext c'
  exact hz c'

end GlobalTheory.Mem.Col2.TC
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.KerVal

theorem fm_succ_mem_valQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ (u : B.Word) (μ : I.ι) (i : ℕ), i < (I.rec7 l Z).R.m → ∀ (x : (((I.tw l l0 Z).fm u μ).lat (i + 1)).V) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)), ∃ v' : ValQ O u μ (i + 1), evC O u μ (i + 1) v' = ((I.tw l l0 Z).fm u μ).emb (i + 1) x c' := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hBs hUnf hJets u μ i hi x c'
  obtain ⟨n, hw, hn, hnat, hds⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ ((I.tw l l0 Z).fm u μ) i hi
  have hlam : ∀ j τ, Col2.lamT (B.hcW u) j τ = lamTG ((I.tw l l0 Z).fm u μ) j τ := by
    intro j τ
    unfold Col2.lamT lamTG
    show Col2.shW _ _ = Formalism.L2.Forms.shW (Examples₂.lamOf (B.hcW u τ) j) _
    obtain ⟨c, hc⟩ := B.R.t_odd
    have h1 : (B.R.t + 1) / 2 = c + 1 := by omega
    have h2 : j * (B.R.t + 1) / 2 = j * (c + 1) := by
      rw [show j * (B.R.t + 1) = 2 * (j * (c + 1)) by rw [hc]; ring]; omega
    simp only [Col2.shW, Formalism.L2.Forms.shW]
    congr 1
    funext r
    show _ + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)) = _ - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ)
    rw [h1, h2]
    push_cast
    ring
  have hP : ((x.1 c').1 : Formalism.L2.DIV.Pol B.LL (Tau B.R) (B.R.N (i + 1))) ∈ polV (I.rec7 l Z) u (i + 1) := by
    have h1 := VV_le_WtPol (K := B.LL) (Col2.lamT (B.hcW u) (i + 1)) (x.1 c').2
    have e : (fun τ r => (Col2.lamT (B.hcW u) (i + 1) τ).natW r) = extNu ((I.rec7 l Z).R.N (i + 1)) (nuT (I.rec7 l Z) u i) := by
      funext τ r
      rw [hlam]
      refine (hnat τ r).trans ?_
      congr 1
      funext τ' r'
      exact hw τ' r'
    rw [e] at h1
    exact h1
  refine ⟨Submodule.Quotient.mk ⟨_, hP⟩, ?_⟩
  funext y
  show evP O u μ (i + 1) ⟨_, hP⟩ y = _
  show (∏ τ, (((I.rec7 l Z).chTw u μ).de (i + 1) y τ) ^ (-(((I.rec7 l Z).chTw u μ).sDiv i τ))) *
    GL3Theta.evFr (I.rec7 l Z) (MvPolynomial.map (I.rec7 l Z).what₂.embLL (x.1 c').1) ((O u μ).frm (i + 1) y) = _
  simp only [(O u μ).frm_de (i + 1) hi y]
  rw [hStd.frm u μ (i + 1) y]
  show _ = Formalism.L2.Col.evFr (gramC (1 : Matrix (Fin _) (Fin _) _) (embAt B.embLL B.tauLL)) (shiftOf (Col2.lamT (B.hcW u) (i + 1))) B.embLL (x.1 c').1 y
  refine Eq.trans ?_ (Formalism.L2.Col.evFr_apply _ _ _ _ _).symm
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    exact ((congrArg DomWeight.detShift (hlam (i + 1) τ)).trans (hds τ)).symm
  · exact GlobalTheory.PdvKm.evFr_map _ _ _ _

end GlobalTheory.Mem.KerVal
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.IpMt

theorem ipMt_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow), (∀ F, jM F ∈ (I.fm l u a).ptC) → (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) → (∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F)) ∧ ∀ F, F ≠ 0 → 0 < (I.ipMt l u a F F).re := by
  intro B X I hOk hP l Z u a jM hmem hper
  obtain ⟨j0, hinj, -, hmem0, hper0, hpos⟩ := PerConj.period_conj I hOk hP l Z u a
  have uniq : ∀ z ∈ (I.fm l u a).ptC, ∀ z' ∈ (I.fm l u a).ptC,
      (∀ w, (I.fm l u a).ipP z w = (I.fm l u a).ipP z' w) → z = z' := by
    intro z hz z' hz' h
    by_contra hne
    have h1 := hpos _ (sub_mem hz hz') (sub_ne_zero.2 hne)
    rw [map_sub (I.fm l u a).ipP, LinearMap.sub_apply, h, sub_self] at h1
    simp at h1
  have hj : ∀ G, I.jStd l u a G = jM G := by
    intro G
    have hex : ∃ z, z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w :=
      ⟨jM G, hmem G, fun w => hper w G⟩
    have hs := Classical.epsilon_spec hex
    exact uniq _ hs.1 _ (hmem G) fun w => (hs.2 w).symm.trans (hper w G)
  have hform : ∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F) := by
    intro F G
    rw [TC.ipMt, hj, hj]
  refine ⟨hform, fun F hF => ?_⟩
  have h0 : jM F = j0 F := uniq _ (hmem F) _ (hmem0 F) fun w => (hper w F).symm.trans (hper0 w F)
  have hne : jM F ≠ 0 := by
    rw [h0]
    exact fun h => hF (hinj (h.trans (map_zero j0).symm))
  rw [hform]
  exact hpos _ (hmem F) hne

theorem ipMt_sum {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (F G : (I.perIn u a).Mt B.fields.emb B.embLL) :
    I.ipMt l u a F G = letI := (I.perIn u a).clFin (l.per u a);
      ∑ c, (I.perIn u a).wt c * pairB (I.perIn u a).sgT
        (MvPolynomial.map (starRingEnd ℂ) (F.1 c.1 ((I.perIn u a).S'.rep c))) (G.1 c.1 ((I.perIn u a).S'.rep c)) := by
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  have h := (ipMt_tie I hOk hP l Z u a (PerConj.jM (I.perIn u a) B.fields.emb B.embLL)
    (PerConj.jM_mem _ _ hE (l.per u a) hH)
    (PerConj.period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u))).1 F G
  refine h.trans ?_
  refine (PerConj.petersson_apply B.fields.emb B.embLL (l.per u a) _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (PerConj.ipVal_cev _ _ _ _ _).trans (congrArg (fun p => pairB _ p _) (PerConj.polOf_cev _ _ _ _))

end GlobalTheory.Mem.Col2.IpMt

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.dtTied_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ T : Formalism.L2.Host.DtTied (I.rec7 l Z) (I.cf l Z), ∀ a, T.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ) := by
  intro B X I _ _ l Z
  refine ⟨GlobalTheory.Mem.Col2.dtIsoRational (I.rec7 l Z) (I.cf l Z) I.SQ (MulEquiv.refl _) (fun j => rfl) rfl ?_ (fun z => rfl), fun _ => rfl⟩
  show UOQ B.host I.SQ = _
  ext x
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

structure StdKerTie {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop where
  X_eq : t.X = B.fields
  seam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)
  Pr : HEq t.Pr (B.primes X)
  Ch : HEq t.Ch I.Ch
  sel : HEq t.sel I.sel
  S : t.S = I.S
  word : HEq t.word fun u : B.Word => u
  tup : HEq t.tup I.tup
  cst : HEq t.cst I.cst
  idx : HEq t.idx I.idx
  m2 : t.m2 = B.R.m - 2
  glob : HEq t.glob I.glob
  amb : HEq t.amb (I.J.amb B t.χ)
  δ : t.δ = I.J.δ
  O : I.StdO l Z Y.Qp t.O

namespace StdKerEmpty

end StdKerEmpty

end GlobalTheory.Mem.Col2.TC

end
end
