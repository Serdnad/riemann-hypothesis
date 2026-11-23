module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle067
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle080
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle388
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle196
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
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
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle203
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ConjDict

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ConjWeil

variable {D : D7}

theorem cjOm_apply {S T : HSp D} (om : Om (negSp S) T) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    cjOm om p f = cj id (om (negGA S p.1, p.2) (cj id f)) := rfl

theorem negGA_mem_GQ (V : HSp D) (γ : GA D V) (h : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _)

theorem weil_cjOm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om (negSp S) T) (hw : IsWeilDatumO ψ (negSp S) T χS χT om) :
    IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (cjOm om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f ↔ IsThetaFunO ψ (negSp S) T (cj id f) := fun f => (I.1 f).2.symm
  have thS' : ∀ f : WO S T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO S T → ℂ),
      heisO ψ S T w f = cj id (heisO ψ (negSp S) T w (cj id f)) := fun w f => by
    rw [(I.2 w f).2, cj_id_cj_id]
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [cjOm_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [cjOm_apply, cjOm_apply, hzS w₀ f, cj_id_cj_id]
    erw [hw.om_heis _ _ _ _ ((thS f).1 hf)]
    rw [hzS _ (cj id _), cj_id_cj_id, actO_negS, MulEquiv.symm_apply_apply]
  · intro γ hγ γ' hγ' f hf
    rw [cjOm_apply]
    show starRingEnd ℂ (om (negGA S γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [cjOm_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (negGA S p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [cjOm_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he (negGA S g) h
      (by unfold SuppAt; rw [mt_negGA]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (negGA S g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ (negSp S) T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        have e1 := hzS u (cj id f')
        rw [cj_id_cj_id] at e1
        rw [← e1, hℓ u hu (cj id f') ((thS' f').1 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← cjOm_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem vac_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (Γ : AddSubgroup (WO S T)) (f : WO S T → ℂ) :
    VacG ψ (negSp S) T Γ f ↔ VacG ψ S T Γ (star f) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S T
  have e0 : star f = cj id f := rfl
  have th : IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hz : ∀ w : WO S T, heisO ψ (negSp S) T w f = f ↔ heisO ψ S T w (cj id f) = cj id f := fun w => by
    have := (I.2 w (cj id f)).2
    rw [cj_id_cj_id] at this
    rw [this]
    exact ⟨fun h => by have := congrArg (cj id) h; rwa [cj_id_cj_id] at this, fun h => by rw [h, cj_id_cj_id]⟩
  rw [e0]
  unfold VacG IsLatVac
  simp only [th, hz]

theorem conj_dict : GlobalTheory.SepRows.DepFixed → All fun {D} _ {L} _ {G} W _ => ∀ i, i < D.R.m → IsWeilDatumO W.ψ _ _ (G.chrS (.chi i 0))⁻¹ (G.chrT (.chi i 0))⁻¹ (omRow W i) ∧ IsWeilDatumO W.ψ _ _ (G.chrS (.core i))⁻¹ (G.chrT (.core i))⁻¹ (omCore W i) ∧ (∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f)) ∧ (∀ f, VacG W.ψ _ _ (latCore G i) f ↔ Dep W (.core i) (star f)) ∧ (∀ g h f, omRow W i (g, h) f = star (W.om (.chi i 0) (negGA _ g, h) (star f))) ∧ (∀ g h f, omCore W i (g, h) f = star (W.om (.core i) (negGA _ g, h) (star f))) ∧ ∀ f, VacG W.ψ _ _ (latRow G i) f → ∀ k ∈ lev G (.grid i 0), omRow W i (1, k) f = f := by
  intro h1 D hq T L μ0 hL sc G W M hM i hi
  have hv : ∀ f, VacG W.ψ _ _ (latRow G i) f ↔ Dep W (.chi i 0) (star f) := fun f =>
    ((vac_star W.ψ_std (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (latRow G i) (star f)).trans
      (by rw [star_star])).symm
  refine ⟨weil_cjOm W.ψ (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) _ _ _ (W.om_is (.chi i 0) ⟨hi, Nat.zero_le _⟩),
    weil_cjOm W.ψ (G.V (.core (i + 1))) (G.V (.core i)) _ _ _ (W.om_is (.core i) hi), hv, fun f =>
    ((vac_star W.ψ_std (G.V (.core (i + 1))) (G.V (.core i)) (latCore G i) (star f)).trans (by rw [star_star])).symm,
    fun g h f => rfl, fun g h f => rfl, fun f hf k hk => ?_⟩
  have e := h1 D hq T L μ0 hL sc G W M hM i hi (.chi i 0) (Or.inl rfl) (star f) ((hv f).1 hf) k hk 1 (one_mem _)
  show star (W.om (.chi i 0) (G.toPair (.chi i 0) k 1) (star f)) = f
  rw [e, star_star]

end GlobalTheory.ConjDict

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceCompress

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_half_idem (v : FinPl D) (h : (2 : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ b : AE D, finPart D b ∈ intAE D ∧ b + b = idem D (.inl v) := by
  have h2 : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ ∈ v.adicCompletionIntegers D.host.F :=
    GlobalTheory.LatVac.half_mem_adicCompletionIntegers D.host.F v h
  have hsum : algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ +
      algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹ = 1 := by
    rw [← map_add (f := _), ← two_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v
      (algebraMap D.host.F (Fv D.host.F v) (2 : D.host.F)⁻¹)), ?_, ?_⟩
  · unfold intAE finPart
    refine AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v ⟨_, h2⟩, 1, ?_⟩
    simp [GlobalTheory.SplitIdem.placeHom, Algebra.TensorProduct.algebraMap_apply] <;> rfl
  · rw [← map_add (f := _), ← map_add (f := _), hsum]
    rfl

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
  {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem exists_char_act (v : FinPl D) {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v)
    (hi : idem D (.inl v) • u = u) :
    ∃ y : AF D.host.F, ∀ f, IsLatVac (heisO ψ S T) (latO S T LS LT fun w => w = v) f →
      heisO ψ S T u f = ψ y • f := by
  classical
  have hidem := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.2.1 v
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨e, hee, hec, hsum, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    have hsum' : e + cA D e = idem D (.inl v) := by rw [hsum]; rfl
    have hsp : IsSplitIdem D e := by
      unfold IsSplitIdem
      exact ⟨hee, hec, v, _, hidem.2.2, hsum⟩
    have hsp' : IsSplitIdem D (cA D e) := isSplitIdem_conj hsp
    have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
    have hint : finPart D e ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])
    have hint' : finPart D (cA D e) ∈ intAE D :=
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hcc])
    have hm1 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e hint u hu
    have hm2 := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ (cA D e) hint' u hu
    have hh1 : IsHalf e (e • u) := (isHalf_iff e (e • u)).2 (by rw [smul_smul, hee])
    have hh2 : IsHalf (cA D e) (cA D e • u) := (isHalf_iff (cA D e) (cA D e • u)).2 (by rw [smul_smul, hcc])
    have hsplit : e • u + cA D e • u = u := by rw [← add_smul, hsum', hi]
    refine ⟨-symplOH S T (e • u) (cA D e • u), fun f hf => ?_⟩
    unfold IsLatVac at hf
    have k1 := hf.2 e hsp _ hm1 hh1
    have k2 := hf.2 _ hsp' _ hm2 hh2
    have key := heisO_heisO ψ S T (e • u) (cA D e • u) f
    rw [k2, k1, hsplit] at key
    conv_rhs => rw [key]
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul]
  · obtain ⟨b, hb, hbb⟩ := exists_half_idem v h2
    refine ⟨0, fun f hf => ?_⟩
    unfold IsLatVac at hf
    have hm := GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ b hb u hu
    have h2u : 2 • (b • u) = u := by rw [two_nsmul, ← add_smul, hbb, hi]
    rw [AddChar.map_zero_eq_one, one_smul, ← h2u]
    exact hf.1 _ hm

private theorem ipO_smul_smul' {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (a b : ℂ)
    (f g : Mx D m n → ℂ) : ipO μ 𝓕 (a • f) (b • g) = (a * starRingEnd ℂ b) * ipO μ 𝓕 f g := by
  unfold ipO
  rw [← integral_const_mul]
  congr 1
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem compress_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (w : WO S T), ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inl v) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ S T ΛS ΛT μ 𝓕 hψ hS hT hμ v w
  classical
  have hn : ∀ a, ‖ψ a‖ = 1 := by
    have h := hψ
    unfold IsStdChar IsCharAF at h
    exact h.1.2.1
  obtain ⟨hI1, -, hI3, hI4, -⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  obtain ⟨ι, hι⟩ : ∃ ι, ι = idem D (.inl v) := ⟨_, rfl⟩
  have hιι : ι * ι = ι := by rw [hι]; exact hI1 _
  have hcι : cA D ι = ι := by rw [hι]; exact hI3 _
  have hinf : infPart D ι = 0 := by rw [hι]; exact (hI4 v).1
  obtain ⟨x, hx⟩ : ∃ x, x = ι • w := ⟨_, rfl⟩
  rw [wAt_eq_smul, ← hι, ← hx]
  have hιx : ι • x = x := by rw [hx, smul_smul, hιι]
  have hloc : ∀ u ∈ latO S T ΛS ΛT (fun _ => True), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => Sum.inl.inj h'.2) h
  have hloc' : ∀ u ∈ latO S T ΛS ΛT (fun u => u = v), ι • u ∈ latO S T ΛS ΛT (fun u => u = v) := by
    intro u hu
    have h := ((GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun u => u = v) u hu) (.inl v)).1
    rw [wAt_eq_smul, ← hι] at h
    exact latO_mono (fun v' h' => h'.1) h
  have hpair : ∀ a, symplO S T (ι • a) x = symplO S T a x := by
    intro a
    rw [symplO_smul, hcι, hιx]
  by_cases hA : ∀ l ∈ latO S T ΛS ΛT (fun u => u = v), ψ (symplO S T l x) = 1
  · have hxg : x ∈ latO S T ΛS ΛT (fun _ => True) := by
      refine ((GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1 x ?_).2 ?_
      · rw [hx]
        ext i j
        simp [Matrix.map_apply, Matrix.smul_apply, map_mul, hinf]
      · intro u' hu'
        rw [symplO_skew, AddChar.map_neg_eq_inv, ← hpair, hA _ (hloc u' hu'), inv_one]
    have hxv : x ∈ latO S T ΛS ΛT (fun u => u = v) := by
      rw [← hιx]
      exact hloc x hxg
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v hxv (by rw [← hι]; exact hιx)
    refine ⟨starRingEnd ℂ (ψ y), fun f g hf hg hvf hvg => ?_⟩
    rw [hy f hvf]
    exact ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g f hg hf).2.2.1 (ψ y)).2
  · push_neg at hA
    obtain ⟨l, hl, hl1⟩ := hA
    have hιl : ι • (ι • l) = ι • l := by rw [smul_smul, hιι]
    obtain ⟨y, hy⟩ := exists_char_act (ψ := ψ) v (hloc' l hl) (by rw [← hι]; exact hιl)
    refine ⟨0, fun f g hf hg hvf hvg => ?_⟩
    rw [zero_mul]
    have hxf : IsThetaFunO ψ S T (heisO ψ S T x f) :=
      (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 x f hf
    have hU := ((GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ g (heisO ψ S T x f) hg hxf).2.2.2.2.2.2.1 (ι • l)).1
    rw [hy g hvg, heisO_comm, hy f hvf, heisO_smul, smul_smul, ipO_smul_smul', map_mul] at hU
    have hc : ψ y * starRingEnd ℂ (ψ y) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
      norm_num
    have hs : starRingEnd ℂ (ψ (symplO S T (ι • l) x)) ≠ 1 := by
      rw [hpair]
      intro h
      exact hl1 ((starRingEnd ℂ).injective (by rw [h, map_one]))
    have h0 : (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) - 1) * ipO μ 𝓕 g (heisO ψ S T x f) = 0 := by
      linear_combination hU - (starRingEnd ℂ (ψ (symplO S T (ι • l) x)) * ipO μ 𝓕 g (heisO ψ S T x f)) * hc
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hs)

end GlobalTheory.PlaceCompress
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_integralSiegelParabolic_of_conjugateIdempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (d : ℕ) (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ Eid : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), Eid * Eid = Eid → Eid + cA σ Eid = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    Eid * cA σ Eid = 0 →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ s ∈ GlobalTheory.InertDbl.ParD σ W v,
      GlobalTheory.InertDbl.matD s * diagCols (Fin d) =
        diagCols (Fin d) * ((1 - (⅟2 : AF F) • Eid) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) ∧
      GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d =
        GlobalTheory.InertDbl.antiCols d * ((1 + cA σ Eid) • (1 : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) := by
  first | exact @GlobalTheory.SplitConjPar.exists_par | exact GlobalTheory.SplitConjPar.exists_par | (intros; apply GlobalTheory.SplitConjPar.exists_par <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGenLeft

open GlobalTheory.InertDbl GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_smul_eq {n : Type} {v : Pl (F := F)} {c : AE F E} (hc : ∀ z : AE F E, At (evFin F v) z → c * c * z = z)
    {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : (c * c) • X = X := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hc _ fun u hu => by simpa using congrFun (congrFun (hX u hu) i) j

theorem inlD_mem_closure_of_split {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl (F := F))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) :
    inlD σ W k ∈ Subgroup.closure (ParD σ W v ∪ NabD σ W v) := by
  obtain ⟨c, hcσ, hcat, hcsq, hclat⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hv
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ d W v h2 c hcσ hcat (hclat d W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ d W v h2 c hcσ (hclat d W) k hk
  have e1 : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e2 : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hsq : (c * c) • (mat k - 1) = mat k - 1 := sq_smul_eq hcsq hk.1
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E d c (mat k) (mat k⁻¹) e1 e2 hsq
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E d c (mat k) (mat k⁻¹) e1 hsq
  let t : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, mul_eq_one_comm.1 ht⟩
  have hq : n⁻¹ * (p * inlD σ W k) ∈ ParD σ W v := by
    refine ⟨KAtD_mul (KAtD_inv hn.1) (KAtD_mul hp.1 (inlD_mem hk)), t, ?_⟩
    have en : matD n⁻¹ * matD n = 1 := (n.1).inv_val
    show matD n⁻¹ * (matD p * matD (inlD σ W k)) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    rw [matD_inlD, hpm]
    rw [← hnm] at hid
    erw [Matrix.mul_assoc, hid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, en, Matrix.one_mul]
    rfl
  have e : inlD σ W k = p⁻¹ * (n * (n⁻¹ * (p * inlD σ W k))) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl hp)))
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hn)) (Subgroup.subset_closure (Or.inl hq)))

theorem inlD_mem_closure_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv _ h2 k hk
  exact inlD_mem_closure_of_split hT.base G.V' v hv h2 k hk

end GlobalTheory.SplitDblGenLeft
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityMap_realTranslate_eq_rightTranslation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  first | exact @GlobalTheory.SmoothTranslate.translate | exact GlobalTheory.SmoothTranslate.translate | (intros; apply GlobalTheory.SmoothTranslate.translate <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

noncomputable section

namespace GlobalTheory.FinFockLin

theorem finF_lin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X),
  IsFinF ψ θ ε A B 0 ∧ (∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g)) ∧
  (∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f)) ∧
  (∀ f g P, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g →
    fockF ψ θ ε A B (f + g) P = fockF ψ θ ε A B f P + fockF ψ θ ε A B g P) ∧
  ∀ (c : ℂ) f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B (c • f) P = c • fockF ψ θ ε A B f P := by
  intro D ψ θ hψ hθ ε M X A B
  have hsm : ∀ (c : ℂ) f, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B (c • f) := by
    intro c f hf
    refine ⟨GlobalTheory.OrientedHeis.theta_smul c hf.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z c hf.1, hf.2 τ z, smul_zero]
  have hadd : ∀ f g, IsFinF ψ θ ε A B f → IsFinF ψ θ ε A B g → IsFinF ψ θ ε A B (f + g) := by
    intro f g hf hg
    refine ⟨GlobalTheory.OrientedHeis.theta_add hf.1 hg.1, fun τ z => ?_⟩
    rw [GlobalTheory.FockIndep.annih_add hψ hθ τ _ z hf.1 hg.1, hf.2 τ z, hg.2 τ z, add_zero]
  have h0 : IsFinF ψ θ ε A B 0 := by
    refine ⟨GlobalTheory.OrientedHeis.theta_zero, fun τ z => ?_⟩
    have h := GlobalTheory.FockIndep.annih_smul hψ hθ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ)) z 0
      (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε M) (T := X))
    simpa only [zero_smul] using h
  refine ⟨h0, hadd, hsm, fun f g P hf hg => ?_, fun c f P hf => ?_⟩
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb 1 hf.1 hg.1 P
    rw [one_smul, one_smul] at h
    exact h
  · have h := GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ (sgn ε M) X hψ hθ (frSgn ε A).cart A.onb B.cart B.onb c hf.1
      h0.1 P
    rw [add_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ _ _ hψ hθ, add_zero] at h
    exact h

end GlobalTheory.FinFockLin

end
end
