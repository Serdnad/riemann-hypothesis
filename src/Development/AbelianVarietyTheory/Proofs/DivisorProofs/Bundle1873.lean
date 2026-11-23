module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle063
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU

theorem conj_div_norm_zpow (u : ℂ) (hu : u ≠ 0) (k : ℤ) :
    (starRingEnd ℂ u / ((‖starRingEnd ℂ u‖ : ℝ) : ℂ)) ^ (-k) = (u / ((‖u‖ : ℝ) : ℂ)) ^ k := by
  have h0 : ((‖u‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hu)
  rw [Complex.norm_conj, _root_.zpow_neg, ← _root_.inv_zpow]
  congr 1
  rw [inv_div, div_eq_div_iff ((map_ne_zero _).2 hu) h0, Complex.mul_conj', sq]

theorem piInf_eq {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (τ : D.what₂.Tau) (w : InfinitePlace D.host.F)
    (h : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding) (y : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) y = starRingEnd ℂ (θ τ (infPart D y)) := by
  have hr : ∀ a : Ainf D.host.F, InfinitePlace.Completion.extensionEmbedding w (GlobalTheory.AutFunCompare.evW w a) =
      starRingEnd ℂ (θ τ (a ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    intro a
    refine DenseRange.induction_on (InfiniteAdeleRing.denseRange_algebraMap D.host.F) a (isClosed_eq ?_ ?_) fun f => ?_
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)
    · exact Complex.continuous_conj.comp (hθ τ).2
    · rw [(GlobalTheory.AutFunCompare.evW w).commutes]
      have e1 := InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm f)
      have e2 : θ τ (algebraMap D.host.F (Ainf D.host.F) f ⊗ₜ[D.host.F] (1 : D.host.E)) = tauE D τ (algebraMap D.host.F D.host.E f) := by
        rw [← (hθ τ).1, ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
      rw [e2]
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]
      refine e1.trans ?_
      exact (RingHom.congr_fun h f).symm
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, map_add (starRingEnd ℂ)]
  | tmul a x =>
    have e : θ τ (fstA D.host.F a ⊗ₜ[D.host.F] x) = θ τ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D τ x := by
      rw [← (hθ τ).1 x, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (a ⊗ₜ[D.host.F] x) =
        infEmb (⟨(starRingEnd ℂ).comp (tauE D τ), h⟩ : EmbOver D.host.E w) (evInf D.host.F w a ⊗ₜ[D.host.F] x) := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, compInf, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    have l2 : infPart D (a ⊗ₜ[D.host.F] x) = fstA D.host.F a ⊗ₜ[D.host.F] x := by
      simp only [infPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    rw [l1, l2, infEmb_tmul, e, map_mul, ← hr]
    rfl

end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

theorem finPart_eq_one {D : D7} (z : AE D) (hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (z - 1)) : finPart D z = 1 := by
  let u : AF D.host.F := ⟨0, 1⟩
  have hu0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
    exact map_zero _
  have h1 := hz u hu0
  have key : ∀ y : AE D, finPart D (u • y) = finPart D y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    | tmul a x =>
      rw [TensorProduct.smul_tmul']
      simp only [finPart, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, smul_eq_mul, map_mul]
      congr 1
      show (1 : Af D.host.F) * sndA D.host.F a = sndA D.host.F a
      exact one_mul _
  rw [← sub_eq_zero, ← RingHom.map_one (finPart D), ← RingHom.map_sub, ← key, h1, RingHom.map_zero]
end GlobalTheory.ConjInfExp

namespace GlobalTheory.ConjInfExp

open GlobalTheory.FockCompare GlobalTheory.AdelicU



theorem hasExp_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  intro D c a ha τf hτf
  choose n hn hθ using ha
  refine ⟨fun w => -n (τf w), ?_, fun w => by push_cast; rw [hn]; ring⟩
  intro z hz
  have hf : finPart D (z : AE D) = 1 := finPart_eq_one _ hz
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  let θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) := fun τ => θ' (tauE D τ)
  have hθ0 : IsInfFam θ := fun τ => hθ' _
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ0 (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ0 ρ hρ r1 r0
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  let zx : D.what₂.Tau → ℂˣ := fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom z
  have hzx : ∀ τ, ((zx τ : ℂˣ) : ℂ) = θ τ (infPart D (z : AE D)) := fun τ => rfl
  have hT : z = T.toHomUnits zx :=
    Units.ext (ext _ _ (hf.trans (tf _).symm) fun τ => (ti zx τ).symm)
  have single : ∀ τ (v : ℂˣ), ((c (T.toHomUnits (Pi.mulSingle τ v)) : Circle) : ℂ) =
      ((v : ℂ) / ((‖(v : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    intro τ v
    have h := (hθ τ).2 θ hθ0 (T.toHomUnits (Pi.mulSingle τ v)) (tf _) fun τ' hτ' => by
      show θ τ' (infPart D (t _)) = 1
      rw [ti, Pi.mulSingle_eq_of_ne hτ', Units.val_one]
    rw [h]
    show ((θ τ (infPart D (t _))) / ((‖θ τ (infPart D (t _))‖ : ℝ) : ℂ)) ^ n τ = _
    rw [ti, Pi.mulSingle_eq_same]
  have hprod : ((c z : Circle) : ℂ) = ∏ τ, ((zx τ : ℂ) / ((‖(zx τ : ℂ)‖ : ℝ) : ℂ)) ^ n τ := by
    have e1 : T.toHomUnits zx = ∏ τ, T.toHomUnits (Pi.mulSingle τ (zx τ)) := by
      rw [← map_prod]; congr 1; exact (Finset.univ_prod_mulSingle zx).symm
    have e2 : ((c z : Circle) : ℂ) = Circle.coeHom (∏ τ, c (T.toHomUnits (Pi.mulSingle τ (zx τ)))) := by
      rw [← map_prod, ← e1, ← hT]; rfl
    rw [e2, map_prod]
    exact Finset.prod_congr rfl fun τ _ => single τ (zx τ)
  have hinj : Function.Injective τf := fun w1 w2 h => by
    have e : w1.embedding = w2.embedding := by rw [← hτf w1, ← hτf w2, h]
    rw [← InfinitePlace.mk_embedding w1, ← InfinitePlace.mk_embedding w2, e]
  have hbij : Function.Bijective τf := (Fintype.bijective_iff_injective_and_card τf).2
    ⟨hinj, (Fintype.card_of_bijective (GlobalTheory.CMTypePlaces.places_bijective D)).symm⟩
  rw [hprod]
  symm
  refine Fintype.prod_bijective τf hbij _ _ fun w => ?_
  beta_reduce
  rw [piInf_eq θ hθ0 (τf w) w (hτf w), ← hzx]
  exact conj_div_norm_zpow _ (zx (τf w)).ne_zero _

end GlobalTheory.ConjInfExp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.LatticeAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Gd (v : HeightOneSpectrum (𝓞 F)) (x : AF F) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) x ∧ evFin F v x ∈ v.adicCompletionIntegers F

theorem gd_zero (v : HeightOneSpectrum (𝓞 F)) : Gd v (0 : AF F) :=
  ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩

theorem gd_add {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x) (hy : Gd v y) : Gd v (x + y) :=
  ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩

theorem gd_neg {v : HeightOneSpectrum (𝓞 F)} {x : AF F} (hx : Gd v x) : Gd v (-x) :=
  ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem hx.2⟩

theorem gd_mul {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x)
    (hy : evFin F v y ∈ v.adicCompletionIntegers F) : Gd v (x * y) :=
  ⟨fun u hu => by rw [← smul_mul_assoc, hx.1 u hu, zero_mul], by rw [map_mul]; exact mul_mem hx.2 hy⟩

theorem ev_alg (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := AlgHom.commutes _ y

def bil (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm (AF F) (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  LinearMap.mk₂ (AF F) (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY))
    (fun x x' y => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem symp_incM (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E)
    (JY : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F y) = algebraMap F (AF F) (symp σ ξ JX JY x y) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [symp, symp, ← ht]

  simp only [hTens, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hc, map_mul, map_sum]

end GlobalTheory.LatticeAtPlace

namespace GlobalTheory.LatticeAtPlace

theorem coords_symp_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) (ξ : E) (v : HeightOneSpectrum (𝓞 F))
    (co : (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F),
    (∀ x, co (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k))) →
    (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) →
    (∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (GlobalTheory.WeilM.symp σ ξ JX JY t t') ∈ v.adicCompletionIntegers F) →
    ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t},
      (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).1 k) ∧ evFin F v ((co γ).1 k) ∈ v.adicCompletionIntegers F ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).2 k) ∧ evFin F v ((co γ).2 k) ∈ v.adicCompletionIntegers F) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∧
        evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ n d JX JY ξ v co T₀ yf zf hco hyz hs γ hγ
  set S : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := {z | ∃ a : AF F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t} with hS
  have hcoord : ∀ z ∈ AddSubgroup.closure S, ∀ k, Gd v ((co z).1 k) ∧ Gd v ((co z).2 k) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha1, ha2, t, ht, rfl⟩ := hz
      intro k
      rw [map_smul, hco]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact ⟨gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).1),
        gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).2)⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨gd_zero v, gd_zero v⟩
    | add x y _ _ hx hy =>
      intro k
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨gd_add (hx k).1 (hy k).1, gd_add (hx k).2 (hy k).2⟩
    | neg x _ hx =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨gd_neg (hx k).1, gd_neg (hx k).2⟩
  have hgen : ∀ x ∈ S, ∀ y ∈ S, Gd v (bil σ ξ JX JY x y) := by
    rintro _ ⟨a, ha1, ha2, t, ht, rfl⟩ _ ⟨b, -, hb2, t', ht', rfl⟩
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    have e : bil σ ξ JX JY (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t') =
        algebraMap F (AF F) (symp σ ξ JX JY t t') := symp_incM σ ξ JX JY t t'
    rw [e]
    refine gd_mul ⟨ha1, ha2⟩ ?_
    rw [map_mul, ev_alg]
    exact mul_mem hb2 (hs t ht t' ht')
  have hpair : ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, Gd v (bil σ ξ JX JY x y) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => rw [map_zero]; exact gd_zero v
      | add y y' _ _ h h' => rw [map_add (f := _)]; exact gd_add h h'
      | neg y _ h => rw [map_neg]; exact gd_neg h
    | zero => intro y _; rw [map_zero, LinearMap.zero_apply]; exact gd_zero v
    | add x x' _ _ h h' => intro y hy; rw [map_add (f := _), LinearMap.add_apply]; exact gd_add (h y hy) (h' y hy)
    | neg x _ h => intro y hy; rw [map_neg, LinearMap.neg_apply]; exact gd_neg (h y hy)
  have hp := hpair γ hγ γ hγ
  exact ⟨fun k => ⟨(hcoord γ hγ k).1.1, (hcoord γ hγ k).1.2, (hcoord γ hγ k).2.1, (hcoord γ hγ k).2.2⟩, hp.1, hp.2⟩

end GlobalTheory.LatticeAtPlace
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VacExpand

theorem symp_add_self_expand : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ γ' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ') =
        GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                     (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ' +
          2 * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY θ hθ γ γ'
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hcc : ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hinv]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcI : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR]
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) ≃ₐ[AF F] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
    AlgEquiv.ofAlgHom (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
  have htr : ∀ z, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z := fun z => Algebra.trace_eq_of_algEquiv e z
  set A := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J with hA
  set Bm := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J with hBm
  set c := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ with hc
  have key : ∀ f : Fin n → Fin d → Fin n → Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    intro f
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  have hconj : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      c (GlobalTheory.WeilM.hTens c A Bm x y) = -GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y

    simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, hcc, hA, hBm, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hcI,
    hX.herm, hY.skew, map_neg]
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.hTens c A Bm (x + y) (x + y) = GlobalTheory.WeilM.hTens c A Bm x x + GlobalTheory.WeilM.hTens c A Bm y y +
        GlobalTheory.WeilM.hTens c A Bm x y + GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    simp only [GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hθ' : σ θ = 1 - θ := eq_sub_of_add_eq' hθ
  have hcΘ : c (inclR (F := F) (AF F) θ) = 1 - inclR (F := F) (AF F) θ := by
    rw [hc, hcI, hθ', map_sub, map_one]
  have hswap : Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ γ') +
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((-1) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
    have h1 : GlobalTheory.WeilM.hTens c A Bm γ' γ = -c (GlobalTheory.WeilM.hTens c A Bm γ γ') := by rw [hconj]; ring
    have h2 : inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ =
        -c ((1 - inclR (F := F) (AF F) θ) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
      rw [h1, map_mul, ← hcΘ, hcc]; ring
    rw [h2, map_neg, htr]
    simp only [sub_mul, one_mul, neg_mul, map_sub, map_neg]
    ring
  simp only [GlobalTheory.WeilM.symp]
  rw [hexp, mul_add, mul_add, mul_add, map_add (f := _), map_add (f := _), map_add (f := _), hswap]
  ring

end GlobalTheory.VacExpand
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory

theorem exists_int_add_conj_eq_one_of_base_good : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LatVac

theorem exists_integer_add_conj_eq_one_of_isGood : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.IsGood σ → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance

end GlobalTheory.LatVac
end
