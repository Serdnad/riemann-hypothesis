module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle223
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumIsFockVacuum
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroup
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
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.heckeChar_unramified_at_cofinitely_many_places : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  first | exact @GlobalTheory.HeckeFinRam.finite_ramified | exact GlobalTheory.HeckeFinRam.finite_ramified | (intros; apply GlobalTheory.HeckeFinRam.finite_ramified <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

theorem _root_.GlobalTheory.T.lowestKType_lieWord_normBound : LieBound := by
  first | exact @GlobalTheory.SepReal.lieBound | exact GlobalTheory.SepReal.lieBound | (intros; apply GlobalTheory.SepReal.lieBound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

namespace GlobalTheory.ConjPlaceRed

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_conj_zero (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (hs : resS F w s = 0) : resS F w' t = 0 := by
  let σ : Formalism.L2.Herm.intAf F E →+* Formalism.L2.Herm.intAf F E :=
    ((Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)).comp
      (Formalism.L2.Herm.intAf F E).subtype).codRestrict _ (fun x => GlobalTheory.ResConjPlace.conj_mem_int τ x.2)
  have hts : t = σ s := Subtype.ext ht
  have h3 : idS F w.asIdeal ≤ (idS F w'.asIdeal).comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun c hcw => ?_
    obtain ⟨c', hc', hcc⟩ := hc c hcw
    have : σ (oToS F E c) = oToS F E c' := by
      apply Subtype.ext
      show τ (c : E) ⊗ₜ[F] _ = (c' : E) ⊗ₜ[F] _
      rw [hcc]; rfl
    rw [Ideal.mem_comap, Ideal.mem_comap, this]
    exact Ideal.mem_map_of_mem _ hc'
  rw [hts]
  rw [GlobalTheory.GeoActCompare.resS_eq_resI, GlobalTheory.GeoActCompare.resI_eq_zero_iff] at hs ⊢
  exact h3 hs

theorem resS_conj_ite (τ : E →ₐ[F] E) (w w' : Pl E)
    (hc : ∀ c ∈ w.asIdeal, ∃ c' ∈ w'.asIdeal, (c' : E) = τ (c : E)) (s t : Formalism.L2.Herm.intAf F E)
    (ht : (t : E ⊗[F] Formalism.L2.Herm.Af F) = Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (s : E ⊗[F] Formalism.L2.Herm.Af F))
    (b : Prop) [Decidable b] (hs : resS F w s = if b then 1 else 0) : resS F w' t = if b then 1 else 0 := by
  let c : Formalism.L2.Herm.intAf F E := if b then 1 else 0
  have hc1 : resS F w c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hc2 : resS F w' c = if b then 1 else 0 := by
    simp only [c]; split_ifs <;> simp
  have hcs : Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) (c : E ⊗[F] Formalism.L2.Herm.Af F) = (c : E ⊗[F] Formalism.L2.Herm.Af F) := by
    simp only [c]; split_ifs <;> simp
  have h0 := resS_conj_zero τ w w' hc (s - c) (t - c) (by
    rw [AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, map_sub, ht, hcs]) (by
    rw [map_sub, hs, hc1, sub_self])
  rw [map_sub, sub_eq_zero, hc2] at h0
  exact h0

end General

variable {D : D7}

theorem crdLat_eq_latFrame (V : HSp D) : Formalism.L2.Herm.crdLat V V.L0 = GlobalTheory.PlaceModel.latFrame V := by
  ext y
  rw [GlobalTheory.PlaceModel.mem_latFrame]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have e : ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i = v := V.frame.sum_equivFun v
    show ∑ i, (Formalism.L2.Herm.crd V v) i • V.frame i ∈ V.L0
    rw [e]; exact hv
  · intro hy
    refine ⟨_, hy, ?_⟩
    show V.frame.equivFun (∑ i, y i • V.frame i) = y
    rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

end GlobalTheory.ConjPlaceRed

namespace GlobalTheory.ConjPlaceRed

theorem Lv_eq_latFrame (D : D7) : Formalism.L2.SG.InstExistsPf.Lv D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := by
  ext y
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv]
  exact (GlobalTheory.PlaceModel.mem_latFrame (Yc D 0) y).symm

theorem mem_Lf (D : D7) (v : Fin (Yc D 0).rank → EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.PlaceModel.latFrame (Yc D 0)) ↔
      v ∈ lamAf (F := D.host.F) (Formalism.L2.SG.InstExistsPf.Lv D) := by
  rw [Lv_eq_latFrame]
  exact (Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (GlobalTheory.PlaceModel.latFrame (Yc D 0))) v).symm

theorem mem_St_of_Kset (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (hβ : IsFrame β (GlobalTheory.PlaceModel.latFrame (Yc D 0))) (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) :
    x.1 ∈ St β := by
  have hS : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat x *ᵥ v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf := hx
  have hSi : ∀ v, v ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
      (((x.1)⁻¹ : GL (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n) _) : Matrix _ _ _) *ᵥ v ∈
        (Formalism.L2.SG.InstExistsPf.instOf D).Lf :=
    (Formalism.UG.stabGL (Formalism.L2.SG.InstExistsPf.instOf D).Lf).inv_mem hx
  refine (GlobalTheory.LevSplit.mem_St_iff β _ hβ (x.1 : GL (Fin (Yc D 0).rank) (EAf D))).2 ⟨fun y hy => (mem_Lf D _).2 ((hS y).1 ((mem_Lf D y).1 hy)),
    fun y hy => (mem_Lf D _).2 ((hSi y).1 ((mem_Lf D y).1 hy))⟩



theorem redFn_conj_eq_one : ∀ (D : D7) (β : GL (Fin (Yc D 0).rank) (EAf D)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf)
    (PP PP' : Formalism.L2.DIV.Pl D.host.E),
    IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset →
    _root_.Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' x.1 = 1 → Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  intro D β x PP PP' hβ hx hc h1
  rw [crdLat_eq_latFrame] at hβ
  have hsd := GlobalTheory.PlaceModel.isSelfDualC_latFrame (Yc D 0)
  obtain ⟨m, s, s', hs, hd⟩ := GlobalTheory.LatVacDual.dualFamily D (Yc D 0) _ hsd
  obtain ⟨G, hG⟩ := GlobalTheory.FrameGram.exists_unit_adelic star (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (fun _ => GlobalTheory.LevSplit.sigR_int) (fun _ => rfl) (Yc D 0).gram β _ hβ (fun y hy => (hsd.2 y).1 hy) s s' hs hd
  obtain ⟨h, hh⟩ := mem_St_of_Kset D β x hβ hx
  have hU : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ ∈
      Formalism.UG.UJ (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
        ((Yc D 0).gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) := by
    have e : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype h * β⁻¹ = x.1 := hh
    rw [e]
    exact x.2
  have key := GlobalTheory.FrameMove.conj_gram_sub (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (Formalism.L2.Herm.intAf D.host.F D.host.E) _ β G h hG hU
  rw [← hh, redFn_frGL] at h1 ⊢
  have h1' : Formalism.UG.bc (resS D.host.F PP') h⁻¹ = 1 := by rw [map_inv, h1, inv_one]
  have h2 : Formalism.UG.bc (resS D.host.F PP) (G * h * G⁻¹) = 1 := by
    apply Units.ext
    ext i j
    have hz : resS D.host.F PP' ((h⁻¹).val j i) = if j = i then 1 else 0 := by
      have e : ((Formalism.UG.bc (resS D.host.F PP') h⁻¹ : GL (Fin (Yc D 0).rank) (kP PP')) : Matrix _ _ (kP PP')) j i =
          resS D.host.F PP' ((h⁻¹).val j i) := rfl
      rw [← e, h1', Units.val_one, Matrix.one_apply]
    have h0 := resS_conj_ite D.sp.cm.sig PP' PP hc _ _ (key i j) (j = i) hz
    refine h0.trans ?_
    rw [Units.val_one, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  rw [map_mul, map_mul, map_inv] at h2
  exact conj_eq_one_iff.1 h2

end GlobalTheory.ConjPlaceRed
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.splitPlace_bigCell_exists_admissible_inverse_alt : (∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det) →
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), (∀ i j, σ (W.J j i) = -W.J i j) →
    IsUnit (2 : v.adicCompletionIntegers F) →
    ∀ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) →
      (∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v))) →
      ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
      ∃ Y : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Y ∧
        (∀ z ∈ GlobalTheory.InertSph.latAt W v, Y *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
        Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 ∧
        ∃ M : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), M * (GlobalTheory.DblVac.diagonalBlockOfMatrix g + Y * (⅟(2 : AF F) • ((GlobalTheory.DblVac.matD g).toBlocks₁₁ +
          (GlobalTheory.DblVac.matD g).toBlocks₁₂ - (GlobalTheory.DblVac.matD g).toBlocks₂₁ - (GlobalTheory.DblVac.matD g).toBlocks₂₂))) = 1 ∧
          ∀ z ∈ GlobalTheory.InertSph.latAt W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | exact GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse | (intros; apply GlobalTheory.SplitPlaceBigCell.splitPlace_bigCell_exists_admissible_inverse <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical


theorem _root_.GlobalTheory.T.exists_complexStructure_gaussVacuum_isFockVacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
        ∀ f₀ : SInf F (Fin n × Fin d), M.IsGauss ψ τ f₀ →
        ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
          (∀ w, J₀ (J₀ w) = -w) ∧ ∀ w x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (J₀ w) ⇑f₀ x =
            Complex.I * GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w ⇑f₀ x := by
  first | exact @GlobalTheory.FockPair.exists_fock_cx | exact GlobalTheory.FockPair.exists_fock_cx | (intros; apply GlobalTheory.FockPair.exists_fock_cx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem lattice_heq_of_eq_hermitianSpaceWithLattice_mk {D : D7} {x : LSp D} {s : HSp D} {l : Submodule (𝓞 D.host.E) (Fin s.rank → D.host.E)}
    (e : x = ⟨s, l⟩) : HEq l x.lat := by subst e; rfl

theorem nodeAgree_grid0_of_weil_over : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ j, j ≤ D.R.m → NodeAgree (GlobalTheory.Grid.row0 R j) W (.grid 0 j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc G' W hW j hj
  rcases Nat.lt_or_ge j D.R.m with h | h
  · rw [← nodeY_eq_chainVertexAtRowZero_of_lt R h]
    have e : G'.node (.grid 0 j) = ⟨Yc D j, R.ΛY j⟩ := colY_lt R.toLevCh h
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, (hW.cartY j h).symm, (hW.onbY j h).symm⟩
  · obtain rfl : j = D.R.m := le_antisymm hj h
    rw [← nodeX_eq_chainVertexAtRowZero_top R]
    have e : G'.node (.grid 0 D.R.m) = ⟨D.sp.X', R.ΛX⟩ := colY_m R.toLevCh
    exact ⟨(congrArg LSp.sp e).symm, lattice_heq_of_eq_hermitianSpaceWithLattice_mk e, hW.cartX.symm, hW.onbX.symm⟩

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}

theorem exists_wRep_of_negSp {S T S' T' : HSp D} (hS : S = S') (hT : T = T') (ψ : AddChar (AF D.host.F) ℂ)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D (negSp S') × GA D T' →* Module.End ℂ (WO (negSp S') T' → ℂ))
    (h : IsWeilDatumO ψ (negSp S') T' χS χT om) :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ true S T χS χT ω ∧ HEq (ω.toSgn true) om := by
  subst hS; subst hT
  let ω : GlobalTheory.Grid.WRep S T :=
    om.comp (((GlobalTheory.Grid.ofSgn true S).symm.toMonoidHom.prodMap (MonoidHom.id _) :
      GA D S × GA D T →* GA D (negSp S) × GA D T))
  have e : ω.toSgn true = om := MonoidHom.ext fun _ => rfl
  refine ⟨ω, ?_, heq_of_eq e⟩
  show IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (ω.toSgn true)
  rw [e]
  exact h

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_omX_of_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ i j, i < D.R.m → j ≤ D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.V (i + 1) j).V (G.V i j).V, GlobalTheory.Grid.IsWeil R.ψ true (G.V (i + 1) j).V (G.V i j).V (G.chiAt (D.R.m - i) (rkV D (i + 1) j)) (G.chiAt (D.R.m - i) (rkV D i j)) ω ∧ HEq (ω.toSgn true) (W.om (.chi i j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hG _ hsp _ i j hi hj
  have hv1 := (hsp.vert (i + 1) j (by omega) hj).sp
  have hv0 := (hsp.vert i j (by omega) hj).sp
  have hom := W.om_is (.chi i j) ⟨by omega, hj⟩
  rw [hW.ψ] at hom
  obtain ⟨ω, h1, h2⟩ := exists_wRep_of_negSp hv1 hv0 R.ψ _ _ (W.om (.chi i j)) hom
  refine ⟨ω, ?_, h2⟩
  have hchi : G.chi (D.R.m - i) = G'.ch.chi (D.R.m - i) := hsp.chi _ (by omega) (by omega)
  have rS : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← hv1]; exact (hG.vert i j (by omega) hj).rank
  have rT : (G'.V (.grid i j)).rank = rkV D i j := by
    rw [← hv0]
    cases i with
    | succ k => exact (hG.vert k j (by omega) hj).rank
    | zero =>
      rw [hv0]
      show (columnBlock R.toLevCh j).sp.rank = _
      simp only [rkV, zero_mul, add_zero]
      rcases hj.eq_or_lt with rfl | hk
      · rw [colY_m]; exact D.sp.X'_rank
      · rw [colY_lt _ hk]
        exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hk.le]; rfl)
  have cS : G'.chrS (.chi i j) = G.chiAt (D.R.m - i) (rkV D (i + 1) j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid (i + 1) j)).rank = _
    rw [rS, ← hchi]
  have cT : G'.chrT (.chi i j) = G.chiAt (D.R.m - i) (rkV D i j) := by
    show Formalism.IndefR.Lift.attChr (G'.ch.chi (D.R.m - i)) R.toLevCh.eta (G'.V (.grid i j)).rank = _
    rw [rT, ← hchi]
  rw [cS, cT] at h1
  exact h1

end GlobalTheory.GridJoin
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JoinArrows

theorem weil_arrow_transport {D : D7} {ψ : AddChar (AF ↥D.host.F) ℂ} {S T S' T' : HSp D}
    (hS : S = S') (hT : T = T') {χS χT χS' χT' : (AE D)ˣ →* Circle} (h1 : χS = χS') (h2 : χT = χT')
    (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS' χT' ω') :
    ∃ ω : GlobalTheory.Grid.WRep S T, GlobalTheory.Grid.IsWeil ψ false S T χS χT ω ∧ HEq ω ω' := by
  cases hS
  cases hT
  cases h1
  cases h2
  refine ⟨ω', ?_, HEq.rfl⟩
  rw [GlobalTheory.Grid.isWeil_false]
  exact h

theorem exists_weil_rowArrow : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) i j, i + 1 ≤ D.R.m → j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.nV i j).V (G.nV i (j + 1)).V, GlobalTheory.Grid.IsWeil R.ψ false (G.nV i j).V (G.nV i (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1))) ω ∧ HEq ω (W.om (.mu t (i + 1) j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G hSp _ hAg _ t i j hi hj

  have hw := W.om_is (.mu t (i + 1) j) ⟨hi, hj⟩
  rw [hW.ψ] at hw

  have e1 : (G.nV i j).V = G'.V (.grid (i + 1) j) := (hAg.vert (i + 1) j hi (by omega)).sp
  have e2 : (G.nV i (j + 1)).V = G'.V (.grid (i + 1) (j + 1)) := (hAg.vert (i + 1) (j + 1) hi hj).sp

  have r1 : (G'.V (.grid (i + 1) j)).rank = rkV D (i + 1) j := by
    rw [← e1]; exact (hSp.vert i j hi (by omega)).rank
  have r2 : (G'.V (.grid (i + 1) (j + 1))).rank = rkV D (i + 1) (j + 1) := by
    rw [← e2]; exact (hSp.vert i (j + 1) hi hj).rank

  have c1 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) j) = G'.chrS (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) j)).rank
    rw [r1]
    rfl
  have c2 : GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D (i + 1) (j + 1)) = G'.chrT (.mu t (i + 1) j) := by
    show _ = Formalism.IndefR.Lift.attChr _ _ (G'.V (.grid (i + 1) (j + 1))).rank
    rw [r2]
    rfl
  exact weil_arrow_transport e1 e2 c1 c2 (W.om (.mu t (i + 1) j)) hw

end GlobalTheory.JoinArrows
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem exists_isWeil_of_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S S' T' Tg : HSp D} (hS : S = S') (hT : Tg = T')
    {χS χT : (AE D)ˣ →* Circle} (ω' : GlobalTheory.Grid.WRep S' T') (h : IsWeilDatumO ψ S' T' χS χT ω') :
    ∃ ω : GlobalTheory.Grid.WRep S Tg, GlobalTheory.Grid.IsWeil ψ false S Tg χS χT ω ∧ HEq ω ω' := by
  subst hS hT
  exact ⟨ω', h, HEq.rfl⟩

theorem omCol_of_weil : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → ∃ ω : GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) ω ∧ HEq ω (W.om (.top t j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F _ _ G' W hW G _ _ hSp _ t j hj
  have hS : (G.Xp j).V = G'.V (.top j) := (hSp.top j hj.le).sp
  have hT : (G.nX j).V = G'.V (.top (j + 1)) := (hSp.top (j + 1) hj).sp
  have hω := W.om_is (.top t j) (show j + 1 ≤ D.R.m from hj)
  have hr : ∀ k, k ≤ D.R.m → Even (G'.V (.top k)).rank := fun k hk => by
    have := (G'.isV (X := .top k) hk (fun _ h => by cases h)).rank
    rw [this]; exact even_rankX D k
  have eS : G'.chrS (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrS, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr j hj.le)]
  have eT : G'.chrT (.top t j) = R.toLevCh.mu t (j + 1) := by
    simp [GlobalTheory.ChiGrid.GridData.chrT, Formalism.IndefR.Lift.attChr, GlobalTheory.ChiGrid.GridData.chr, Nat.not_odd_iff_even.2 (hr (j + 1) hj)]
  rw [eS, eT, hW.ψ] at hω
  exact exists_isWeil_of_eq hS hT _ hω

end GlobalTheory.GridJoin
end
end

section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → ℓ (ω (t, 1) s) = (-1) ^ n' * (q : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') := by
  first | exact @GlobalTheory.SphTheta.TorusFirst.value_torus_first | exact GlobalTheory.SphTheta.TorusFirst.value_torus_first | (intros; apply GlobalTheory.SphTheta.TorusFirst.value_torus_first <;> assumption)
end
