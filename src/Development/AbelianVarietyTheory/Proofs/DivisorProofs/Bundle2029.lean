module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IoOverLeftUnique
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LevModel

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem exists_frBor_of_frOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
    [Algebra d.c₂.F S] {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {p p' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d p y) (h' : FrOver d p' y') (hb : FrBor t p p') : ∃ t' : Ix Dw → Sˣ, FrBor t' y y' := by
  obtain ⟨e, hu, -⟩ := h
  obtain ⟨e', hu', -⟩ := h'
  obtain ⟨ex, au, -⟩ := hb
  refine (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').2.1 (by rw [← e, ← e', ex]) fun τ i => ?_
  obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
  refine ⟨cf, by rw [c₁]; exact (t _).isUnit, c₂, ?_⟩
  have k := (GlobalTheory.FrameLift.comb_iff d.m e (fun j => (p.tan τ j).1) cf (ex ▸ (p'.tan τ i).1)).1 hcf
  rw [funext (hu τ), hu'] at k
  exact k

theorem lact_conj_eq_rmul : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hLev σ₂ hσ₂ k₂ k δ hG hδ hOv γ₂ hγ₂ x hx x' hM
  have hσ : GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) := by
    unfold GoodEmb at hσ₂ ⊢
    rw [← hσ₂]
    rfl
  have hU := hL.unf _ hσ
  have hU₂ := hL₂.unf _ hσ₂
  have hγx : lact γ₂ x ∈ ((U₂ σ₂).X k₂).dom := (ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.lact_mem_dom_iff _ hγ₂ x).2 hx
  obtain ⟨t₀, ht₀⟩ := (hU₂.2.2.2.1 k₂ k₂ ⟨x, hx⟩ ⟨lact γ₂ x, hγx⟩).2
    ⟨γ₂, hγ₂, ExtFPf.oneF _, ExtFPf.oneF_mem _, by rw [ExtFPf.rmul_oneF]⟩
  have hM' : Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ (lact γ₂ x) (lact (MulAut.conj δ γ₂) x') := by
    intro τ h₂ h₁
    have e := hM τ h₂ h₁
    show ((MulAut.conj δ γ₂ : GL _ _) : Matrix _ _ _).map τ * mat x' ⟨τ, h₁⟩ =
      (δ : Matrix _ _ _).map τ * ((γ₂ : Matrix _ _ _).map τ * mat x ⟨τ, h₂⟩)
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul (f := τ), ← Matrix.map_mul (f := τ),
      ← Units.val_mul, ← Units.val_mul, MulAut.conj_apply, inv_mul_cancel_right]
  obtain ⟨hx', t₁, -, y, hy₁, hy₂⟩ := hOv x hx x' hM
  obtain ⟨hx'', t₂, -, y', hy₁', hy₂'⟩ := hOv (lact γ₂ x) hγx _ hM'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  obtain ⟨t', ht'⟩ := exists_frBor_of_frOver d hy₂ hy₂' ht₀
  have G := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid _ H Dw l Xo c (CAt σ₂)
  have hb := G.2.1 _ _ _ _ _ (G.2.1 _ _ _ _ _ hy₁ ht') (G.2.2.1 _ _ _ hy₁')
  obtain ⟨γ, hγ, b, hb', e⟩ := (hU.2.2.2.1 k k ⟨x', hx'⟩ ⟨_, hx''⟩).1 ⟨_, hb⟩
  exact ⟨γ, hγ, b, hb', eq_of_heq (Sigma.mk.inj e).2⟩

end GlobalTheory.LevModel
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)}

theorem isConjAt_conjW (σ : E →ₐ[F] E) (hw : Formalism.UG.IsInertAt F E v w) :
    IsConjAt σ (under_eq_of_isInertAt hw) (conjW σ hw) := fun y => by
  show toCompl _ (sigR (Fv F v) σ ((InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm (toCompl _ y))) = _
  congr 2
  exact (InertChart.complEquiv hw (under_eq_of_isInertAt hw)).symm_apply_apply y

theorem conjW_conjW (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hw : Formalism.UG.IsInertAt F E v w)
    (x : w.adicCompletion E) : conjW σ hw (conjW σ hw x) = x := by
  obtain ⟨y, rfl⟩ := InertChart.toCompl_surjective (under_eq_of_isInertAt hw) x
  rw [isConjAt_conjW σ hw, isConjAt_conjW σ hw]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hσ]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem iotaW_mulVec (hw : Formalism.UG.IsInertAt F E v w) {l m : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (y : m → w.adicCompletion E) :
    (fun i => iotaW hw ((M *ᵥ y) i)) = M.map (iotaW hw) *ᵥ fun i => iotaW hw (y i) := by
  funext i

  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, iotaW_mul]

theorem map_iotaW_mul (hw : Formalism.UG.IsInertAt F E v w) {l m p : Type} [Fintype m]
    (M : Matrix l m (w.adicCompletion E)) (N : Matrix m p (w.adicCompletion E)) :
    M.map (iotaW hw) * N.map (iotaW hw) = (M * N).map (iotaW hw) := by
  ext i j

  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iotaW_mul]

theorem one_map_iotaW (hw : Formalism.UG.IsInertAt F E v w) (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map (iotaW hw) =
      iotaW hw 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem herm_gram {R : Type} [CommRing R] (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, τ (M i j) = M j i) (i j : Fin n) :
    τ ((Formalism.UG.cT τ A * M * A) i j) = (Formalism.UG.cT τ A * M * A) j i := by

  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hτ, hM,
  Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem isUnit_of_val_eq_one {t : Formalism.UG.Ov E w} (ht : Valued.v (t : w.adicCompletion E) = 1) : IsUnit t := by
  have h0 : (t : w.adicCompletion E) ≠ 0 := fun h0 => by rw [h0, map_zero] at ht; exact zero_ne_one ht
  have hm : (t : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
    show _ ∈ w.adicCompletionIntegers E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ht, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

end GlobalTheory.InertLocDict

namespace GlobalTheory.InertLocDict

open GlobalTheory.InertBigCell

theorem exists_local_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∃ (O : Type) (_ : CommRing O) (c : O →+* O) (ι : O →ₙ+* AE F E) (P Q : Matrix (Fin n) (Fin n) (AE F E))
      (JL : Matrix (Fin n) (Fin n) O),
      IsLocalRing O ∧ (∀ x, c (c x) = x) ∧ IsUnit (2 : O) ∧ (∃ x : O, IsUnit (c x - x)) ∧
      Function.Injective ι ∧ At (evFin F v) (ι 1) ∧ (∀ y : AE F E, At (evFin F v) y → ι 1 * y = y) ∧
      (∀ x, cA σ (ι x) = ι (c x)) ∧
      P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧ Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      ι 1 • P = P ∧ ι 1 • Q = Q ∧
      (∀ i j, c (JL j i) = JL i j) ∧ IsUnit JL.det ∧ Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι ∧
      ∀ z : Fin n → AE F E, z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i) := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hw
  have h := under_eq_of_isInertAt hw
  have hc : IsConjAt σ h (conjW σ hw) := isConjAt_conjW σ hw
  have hσ : ∀ x, σ (σ x) = x := InertChart.conj_conj hB.cm
  haveI : IsLocalRing (Formalism.UG.Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
  let c : Formalism.UG.Ov E w →+* Formalism.UG.Ov E w :=
    ((conjW σ hw).comp (Formalism.UG.Ov E w).subtype).codRestrict (Formalism.UG.Ov E w)
      (fun x => InertChart.conj_mem hw hc x.2)
  let ι : Formalism.UG.Ov E w →ₙ+* AE F E :=
    { toFun := fun x => iotaW hw (x : w.adicCompletion E)
      map_mul' := fun x y => iotaW_mul hw _ _
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ _ _ }
  have hι : ∀ x, ι x = iotaW hw (x : w.adicCompletion E) := fun _ => rfl
  have hι1 : ι 1 = iotaW hw 1 := rfl
  have hcv : ∀ x, ((c x : Formalism.UG.Ov E w) : w.adicCompletion E) = conjW σ hw x := fun _ => rfl
  obtain ⟨a, ha⟩ := InertChart.exists_isFrameAt (L := X.L) hw hX.lat.fg (Submodule.IsLattice.span_eq_top (self := hX.lat))
  have hJ : (X.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hX
  obtain ⟨Bm, ⟨k, hk⟩, eB⟩ := InertChart.exists_gram hw hc hJ
    (GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hB hX v) ha
  have hkij : ∀ i j, ((k.1 i j : Formalism.UG.Ov E w) : w.adicCompletion E) = Bm.1 i j := fun i j => by
    rw [← hk]; rfl
  have hBt : Bm.1ᵀ = a.1ᵀ * X.J.map (algebraMap E (w.adicCompletion E)) * a.1.map (conjW σ hw) := by
    rw [eB, Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨Formalism.UG.Ov E w, inferInstance, c, ι, a.1.map (iotaW hw), (a⁻¹).1.map (iotaW hw), k.1ᵀ, inferInstance,
    fun x => Subtype.ext (conjW_conjW σ hσ hw x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h2 : (2 : w.adicCompletion E) ≠ 0 := by
      rw [← map_ofNat (algebraMap E (w.adicCompletion E)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    have hm : (2 : w.adicCompletion E)⁻¹ ∈ Formalism.UG.Ov E w := by
      have := complMap_mem h (GlobalTheory.InertLocField.half_mem v (hB.inert v w hw).1)
      rwa [complMap_algebraMap, map_inv₀, map_inv₀, map_ofNat, map_ofNat] at this
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ h2)⟩
  ·
    obtain ⟨x, hx⟩ := InertChart.exists_conj_sub_unit hB.cm hw
    have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    have hxm : algebraMap E (w.adicCompletion E) (x : E) ∈ Formalism.UG.Ov E w := by
      show _ ∈ w.adicCompletionIntegers E
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hval]; exact w.valuation_le_one x
    refine ⟨⟨_, hxm⟩, ?_⟩
    refine isUnit_of_val_eq_one ?_
    show Valued.v (conjW σ hw (algebraMap E _ (x : E)) - algebraMap E _ (x : E)) = 1
    rw [InertChart.conj_algebraMap hc, ← map_sub, hval, hx]
  · exact fun x y hxy => Subtype.ext (iotaW_injective hw hxy)
  · rw [hι1, iotaW_apply]; exact GlobalTheory.InertLocField.at_liftT v _
  · intro y hy
    have h1 := hy _ (GlobalTheory.InertLocField.evFin_one_sub v)
    rw [sub_smul, one_smul, sub_eq_zero] at h1
    rw [hι1, iotaW_one, ← Algebra.smul_def]
    exact h1.symm
  · intro x
    rw [hι, hι, hcv, iotaW_conjW]
  · rw [map_iotaW_mul, Units.mul_inv, one_map_iotaW, hι1]
  · rw [map_iotaW_mul, Units.inv_mul, one_map_iotaW, hι1]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hι1, ← iotaW_mul, one_mul]
  · intro i j
    apply Subtype.ext
    rw [hcv, Matrix.transpose_apply, Matrix.transpose_apply, hkij, hkij, eB]
    refine herm_gram (conjW σ hw) (conjW_conjW σ hσ hw) a.1 (X.Jᵀ.map (algebraMap E (w.adicCompletion E)))
      (fun p q => ?_) i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, InertChart.conj_algebraMap hc, hX.herm]
  · rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).1 k.isUnit
  · have e1 : (a.1.map (iotaW hw))ᵀ = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        a.1ᵀ.map (iotaW hw) := by
      rw [smul_zero, zero_add, Matrix.transpose_map]
    have e2 : (a.1.map (iotaW hw)).map (cA σ) = (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1)) • (0 : Matrix (Fin n) (Fin n) (AE F E)) +
        (a.1.map (conjW σ hw)).map (iotaW hw) := by
      rw [smul_zero, zero_add]
      ext i j
      simp only [Matrix.map_apply, iotaW_conjW]
    rw [e1, e2, incM_split hw X.J,
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      idem_split_mul _ (iotaW hw) (one_sub_idem v) (one_sub_mul_iotaW hw) (iotaW_mul hw),
      Matrix.zero_mul, Matrix.zero_mul, smul_zero, zero_add, ← hBt]
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, hι, hkij]
  · intro z
    rw [GlobalTheory.InertSphLat.mem_latAt_iff hw X z]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have e : a.1 *ᵥ ((a⁻¹).1 *ᵥ u) = u := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have hint := (ha ((a⁻¹).1 *ᵥ u)).2 (by rw [e]; exact hu)
      refine ⟨fun i => ⟨_, hint i⟩, ?_⟩
      show (fun i => iotaW hw (u i)) = a.1.map (iotaW hw) *ᵥ fun i => iotaW hw (((a⁻¹).1 *ᵥ u) i)
      rw [← iotaW_mulVec, e]
    · rintro ⟨b, rfl⟩
      refine ⟨a.1 *ᵥ fun i => (b i : w.adicCompletion E), (ha _).1 fun i => (b i).2, ?_⟩
      rw [iotaW_mulVec]
      rfl

end GlobalTheory.InertLocDict
end
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isSec_sum_smul_bc {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {m : ℕ} (a : Fin m → ℂ)
    (P : Fin m → Frame X.Ψ r → ℂ) (hP : ∀ i, X.IsSec la (P i)) :
    X.IsSec la (fun x => ∑ i, a i * P i x) := by
  refine ⟨DifferentiableOn.fun_sum fun i _ => (hP i).1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.1 x hx b hb]; ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [(hP i).2.2 γ hγ x hx]; ring

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

open Classical in
theorem rdU_unfExt_of_isBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) {m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hBC : IsBC hle f' as fs) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) f' k x = ∑ i, σ' (as i) * rdU U (fs i) k x := by
  show (if h : x ∈ (U.X k).dom then toC (evR Xo c' f' ((unfExt hle σ' hσ U).un k ⟨x, h⟩)) else 0) =
    ∑ i, σ' (as i) * (if h : x ∈ (U.X k).dom then toC (evR Xo c (fs i) (U.un k ⟨x, h⟩)) else 0)
  by_cases hx : x ∈ (U.X k).dom
  · simp only [dif_pos hx]
    exact @hBC (CAt σ') _ σ.toAlgebra σ'.toAlgebra hσ _
  · simp only [dif_neg hx, mul_zero, Finset.sum_const_zero]

theorem isUnf_unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) {U : Unf Xo c σ r} (hU : IsUnf U) : IsUnf (unfExt hle σ' hσ U) := by
  obtain rfl : σ = σ'.comp (incF c c' hle) := RingHom.ext fun a => (hσ a).symm
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU
  letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
  refine ⟨h1, h2, fun y => ?_, h4, fun a n hd f' hf' k => ?_, h6⟩
  · exact h3 (FrPt.res hle (S := CAt σ') hσ y)
  · obtain ⟨m, as, fs, hfs, hBC⟩ := (secBC_and_cuspBC E H Dw l Xo c c' hle).1 a n f' hf'
    have e : rdU (unfExt hle σ' hσ U) f' k = fun x => ∑ i, σ' (as i) * rdU U (fs i) k x :=
      funext fun x => rdU_unfExt_of_isBC hle σ' hσ U hBC k x
    rw [e]
    exact isSec_sum_smul_bc (U.X k) (laU U a n k) _ _ fun i => h5 a n hd _ (hfs i) k

theorem rdU_unfExt_smul_rulBC (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ)
    (hσ : ∀ a, σ' (incF c c' hle a) = σ a) (U : Unf Xo c σ r) (u : c'.F) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU (unfExt hle σ' hσ U) (u • rulBC hle f) k x = σ' u * rdU U f k x := by
  rw [map_smulₛₗ]
  have e := rdU_unfExt_of_isBC hle σ' hσ U (GlobalTheory.FieldBCModel.isBC_rulBC hle hf.1) k x
  simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_fin_one, map_one, one_mul] at e
  rw [← e]
  rfl

end Gen

theorem cXiAt_covBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ)
    (hs : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0) (h : CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0) :
    CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  obtain ⟨h1, h2, g, e, F, ik, φ, th, h3, h4, h5⟩ := h
  refine ⟨isUnf_unfExt (le_covCoeff hle d) _ (fun _ => rfl) h1, h2, g, e, F, ik, φ, th, h3, h4, fun h γ hm => ?_⟩
  have e1 := rdU_unfExt_smul_rulBC (le_covCoeff hle d)
    (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) (fun _ => rfl) U₂
    (show (covCoeff hle d).F from u) hs (dict₂ h).1 (dict₂ h).2
  refine e1.trans ?_
  rw [h5 h γ hm, ← mul_assoc]
  rfl

end GlobalTheory.OneMapAll
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.DoublingEvaluationL2

theorem partL_lintegral_sq : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL (κ' := κ') A Φ ∈ schA F (κ ⊕ κ')) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ A hmem hA μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hA μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL (κ' := κ') A Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ =
      C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ := by
    intro y
    have h := hC₁ _ (GlobalTheory.DoublingEvLaw.sliceL hΦ y)
    simpa only [partL_apply, Sum.elim_comp_inl, Sum.elim_comp_inr] using h
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DoublingEvaluationL2

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.diagonal_integral_heisenberg_translate_integral_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  first | exact @GlobalTheory.InertLagInd.diagW_box_indicator | exact GlobalTheory.InertLagInd.diagW_box_indicator | (intros; apply GlobalTheory.InertLagInd.diagW_box_indicator <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.doubled_lattice_local_image_full_at_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M.co dd →
    ∀ η : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v,
      (∀ b, ((0 : (Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), b) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) →
        GlobalTheory.LatVac.psiAt B.ψ v (η ⬝ᵥ b) = 1) →
      ∃ y, (η, y) ∈ (latDbl G.V G.W v).map (GlobalTheory.LatVac.locCo dd v) := by
  first | exact @GlobalTheory.DblFill.latDbl_fill | exact GlobalTheory.DblFill.latDbl_fill | (intros; apply GlobalTheory.DblFill.latDbl_fill <;> assumption)
end
