module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankGraphJetsLeChoose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle003
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finrank_graphJets_le_choose : ∀ {κ κ' : Type} [Field κ] [Field κ'] [Algebra ℂ κ] [Algebra ℂ κ'] (k M : ℕ) (ρ : κ →ₐ[ℂ] κ'),
  (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  letI : Algebra κ' (κ ⊗[ℂ] κ') := Algebra.TensorProduct.rightAlgebra;
  Module.finrank κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) ≤
    (M + k - 1).choose k ∧
  Module.Finite κ' ((κ ⊗[ℂ] κ') ⧸ (RingHom.ker (Algebra.TensorProduct.productMap ρ (AlgHom.id ℂ κ'))) ^ M) := by
  first | exact @GlobalTheory.JetDim.jets_finrank_le | exact GlobalTheory.JetDim.jets_finrank_le | (intros; apply GlobalTheory.JetDim.jets_finrank_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem placeEquiv_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c x) := by
  intro k K K' _ _ _ _ c c' e he
  refine ⟨⟨RingEquivTransport.place e he,
    RingEquivTransport.place e.symm (RingEquivTransport.symm_apply e he),
    RingEquivTransport.place_symm_place e he, RingEquivTransport.place_place_symm e he⟩,
    fun E => ⟨RingEquivTransport.apply_mem_place e he E, RingEquivTransport.ord_place e he E,
      RingEquivTransport.ordQ_place e he E, fun n x _ => ?_⟩⟩
  have hd : dForm c' (e ∘ x) = TopForm.formMap n e.toRingHom (RingHom.ext he) (dForm c x) :=
    (TopForm.formMap_dForm e.toRingHom (RingHom.ext he) x).symm
  change (RingEquivTransport.place e he E).formOrd _ = _
  rw [hd]
  exact RingEquivTransport.formOrd_place e he E _

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.ringEquiv_transports_varietyPair_data : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'),
  (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (R : Subring K) (φ : K →₀ ℚ), TrBasis c x →
  TrBasis c' (e ∘ x) ∧
  (IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom)) ∧
  (Klt c n R (dForm c x) φ ↔ Klt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) ∧
  (EffAt c n R (dForm c x) φ ↔ EffAt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) := by
  first | exact @GlobalTheory.FieldPair.transport_ringEquiv | exact GlobalTheory.FieldPair.transport_ringEquiv | (intros; apply GlobalTheory.FieldPair.transport_ringEquiv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ChowHt GlobalTheory.HermTools

namespace GlobalTheory.HilbertSamuel

theorem denseRange_of_not_isReal {K : Type*} [Field K] {σ : K →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · refine absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)) hσ
    obtain ⟨r, hr⟩ := h.le (Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    exact congrArg (fun s : Subfield ℂ => (s : Set ℂ)) h

theorem frameNorm_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (fun j => c * x j) = ‖c‖ * frameNorm A x := by
  change frameNorm A (c • x) = _
  simp only [frameNorm, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Continuous (frameNorm A) := by
  unfold frameNorm Matrix.mulVec dotProduct
  fun_prop

theorem continuous_cnrm {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (h : HermFam K V)
    (σ : K →+* ℂ) (v : ι → V) : Continuous fun c => cnrm h σ c v := by
  unfold cnrm csq
  fun_prop

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_mem_span {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    {S : Set V} (hS : Submodule.span F S = ⊤) (x : V) : ∃ a : F, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 F) S := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 F)) F S x (hS.ge trivial)
  refine ⟨algebraMap (𝓞 F) F t, ?_, by rwa [algebraMap_smul]⟩
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 (nonZeroDivisors.coe_ne_zero t)

namespace Data

variable {X : Data F} {β : (F →+* ℂ) → ℝ}

theorem MulBound.of_field (h : X.MulBound β) {j : ℕ} (hj : j < X.T) (σ : F →+* ℂ) (u : Fin X.N → F) (f : X.V j)
    (g : X.V (j + 1)) (e : (g : X.Sec (j + 1)) = X.mulW j u f) :
    (X.nm (j + 1)).nrm σ g ≤ Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (u k)) * (X.nm j).nrm σ f := by
  obtain ⟨a, ha, hu⟩ := exists_smul_mem_span X.geom.alg.spans u
  obtain ⟨b, hb, hf⟩ := exists_smul_mem_span (X.full j).span f
  rw [Submodule.span_eq] at hf
  have key : (X.nm (j + 1)).nrm σ (a • b • g) ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (a * u k)) * (X.nm j).nrm σ (b • f) :=
    h j hj σ _ hu _ hf (a • b • g) (by
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, e, map_smul, map_smul, LinearMap.smul_apply,
        smul_comm])
  simp only [map_mul, frameNorm_mul, HermFam.nrm_smul_up] at key
  have ha' : 0 < ‖σ a‖ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have hb' : 0 < ‖σ b‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb)
  exact le_of_mul_le_mul_left (by linarith) (mul_pos ha' hb')

theorem MulBound.mulBoundAt_of_not_isReal (h : X.MulBound β) {σ : F →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    X.MulBoundAt σ (β σ) := fun j hj u m c f g hg => by
  have hd := denseRange_of_not_isReal hσ
  refine ((DenseRange.piMap fun _ : Fin X.N => hd).prodMap (DenseRange.piMap fun _ : Fin m => hd)).induction_on
    (p := fun z => cnrm (X.nm (j + 1)) σ (fun t => z.1 t.1 * z.2 t.2) g ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) z.1 * cnrm (X.nm j) σ z.2 f) (u, c) ?_ ?_
  · exact isClosed_le ((continuous_cnrm _ _ _).comp (by fun_prop))
      ((continuous_const.mul ((continuous_frameNorm _).comp continuous_fst)).mul
        ((continuous_cnrm _ _ _).comp continuous_snd))
  · rintro ⟨a, b⟩
    have := h.of_field hj σ a (∑ i, b i • f i) (∑ t : Fin X.N × Fin m, (a t.1 * b t.2) • g t) (by
      conv_rhs => rw [pi_eq_sum_univ' a]

      simp only [Fintype.sum_prod_type, Submodule.coe_sum, Submodule.coe_smul, hg, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _))
    simp only [← cnrm_map, map_mul] at this
    exact this

theorem MulBound.mulBoundAt [_root_.NumberField.IsTotallyComplex F] (h : X.MulBound β) (σ : F →+* ℂ) : X.MulBoundAt σ (β σ) :=
  h.mulBoundAt_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)

end Data

end GlobalTheory.HilbertSamuel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_

  rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]



variable (X) in
theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩




end Data

end GlobalTheory.HilbertSamuel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing
open scoped ComplexConjugate

namespace GlobalTheory

section Points

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {B : LB Y}

theorem CxPts.mem_ptsIn_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

end Points

theorem mem_unitaryGroup_of_norm_mulVec {α : Type*} [Fintype α] [DecidableEq α] {V : Matrix α α ℂ}
    (h : ∀ w : α → ℂ, √(∑ i, ‖V.mulVec w i‖ ^ 2) = √(∑ i, ‖w i‖ ^ 2)) : V ∈ Matrix.unitaryGroup α ℂ := by
  have key := (LinearMap.norm_map_iff_inner_map_map (Matrix.toEuclideanLin V)).1 fun x => by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    exact h x.ofLp
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have := key (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply, Matrix.mul_apply, Matrix.one_apply, mul_comm, Pi.single_apply, eq_comm] using this

theorem exists_unitary_of_frameNorm_conj {N : ℕ} {M M' : Matrix (Fin N) (Fin N) ℂ} (hM : M.det ≠ 0)
    (hM' : M'.det ≠ 0) (h : ∀ x : Fin N → ℂ, frameNorm M' (fun j => conj (x j)) = frameNorm M x) :
    ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, M' = M.map (starRingEnd ℂ) * U := by
  have hV : M'⁻¹ * M.map (starRingEnd ℂ) ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    mem_unitaryGroup_of_norm_mulVec fun w => by
      have := h (M.mulVec fun j => conj (w j))
      have e : (fun j => conj (M.mulVec (fun j => conj (w j)) j)) = (M.map (starRingEnd ℂ)).mulVec w :=
        funext fun j => by simp [Matrix.mulVec, dotProduct]
      rw [e, frameNorm, frameNorm, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul M hM.isUnit, Matrix.one_mulVec] at this
      simpa only [RCLike.norm_conj] using this
  refine ⟨_, Unitary.star_mem hV, ?_⟩
  have e : M.map (starRingEnd ℂ) = M' * (M'⁻¹ * M.map (starRingEnd ℂ)) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M' hM'.isUnit, Matrix.one_mul]
  generalize M'⁻¹ * M.map (starRingEnd ℂ) = V at e hV
  rw [e, Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.1 hV, Matrix.mul_one]

variable {F : Type} [Field F] [NumberField F]

theorem Adelic.HermSys.isConj_weight (T : Adelic.HermSys F) (hb : T.BasePointFree) (hh : T.Hermitian)
    (hc : T.ConjInvariant) (σ : F →+* ℂ) :
    (T.weight hb hh σ).IsConj (T.weight hb hh (ComplexEmbedding.conjugate σ)) := by
  obtain ⟨U, hU, e⟩ := exists_unitary_of_frameNorm_conj (hh σ) (hh (ComplexEmbedding.conjugate σ)) (hc σ)
  exact Weight.isConj_fsBasis_of_unitary _ _ _ _ _ hU e

namespace HilbertSamuel.Geo

variable (G : Geo F)

theorem isConj_φ₂ (σ : F →+* ℂ) : (G.φ₂ σ).IsConj (G.φ₂ (ComplexEmbedding.conjugate σ)) :=
  G.second.isConj_weight _ _ G.conj₂ σ

variable {G}

end HilbertSamuel.Geo

end GlobalTheory
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
open scoped Classical

namespace GlobalTheory.ConjSch

def conjSchwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) : SchwartzMap V ℂ where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjSchwartz_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (x : V) :
    conjSchwartz f x = starRingEnd ℂ (f x) := rfl

theorem conj_mem_schA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, g, hg, rfl⟩ := hΨ
    apply Submodule.subset_span
    refine ⟨conjSchwartz f, fun y => starRingEnd ℂ (g y), ⟨hg.1.comp _, hg.2.comp_left (map_zero _)⟩, ?_⟩
    funext x
    simp [pureA, conjSchwartz_apply, map_mul]
  | zero =>
    convert (schA F κ).zero_mem using 1
    funext x; simp
  | add Ψ₁ Ψ₂ _ _ h₁ h₂ =>
    have := (schA F κ).add_mem h₁ h₂
    convert this using 1
    funext x; simp
  | smul c Ψ _ h =>
    have := (schA F κ).smul_mem (starRingEnd ℂ c) h
    convert this using 1
    funext x; simp

end GlobalTheory.ConjSch

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.SympRight

theorem hTens_eq_trace' {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem symp_mul_transpose_right : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α β β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
    (JA : Matrix α α S) (JB : Matrix β β S) (Q : Matrix β β' S) (z z' : Matrix α β' S),
    symp c ξ JA JB (z * Qᵀ) (z' * Qᵀ) = symp c ξ JA (Qᵀ * JB * Q.map c) z z' := by
  intro R S _ _ _ c ξ α β β' _ _ _ _ _ _ JA JB Q z z'
  simp only [symp, hTens_eq_trace']
  congr 2
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SympRight
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.exists_adelicSchwartz_thetaDistributionSum_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ φ ∈ schA F κ, thetaSum F φ ≠ 0 := by
  first | exact @GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | exact GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero | (intros; apply GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero <;> assumption)
end
