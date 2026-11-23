module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
public import Development.WeilBound.ThetaLifts.Reductions.SiegelAbs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import GroundTheory.AutomorphicForms.ReductionHeight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle677
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.WeilBound.ThetaLifts.Reductions.SiegelHaar

@[expose] public section

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem C1_mul (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c1 (W := W) hn (mm A U) = mm A (c1 (W := W) hn U) := by
  ext i j; rfl

theorem mul_sub_one_mulVec_mem_spL (hn : W.rank + t = n) {a b : ℕ} (A : Mx D a b) (U : Mx D b n) :
    c2 (W := W) hn (mm A U) = mm A (c2 (W := W) hn U) := by
  ext i j; rfl

theorem isOneCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c1 (W := W) hn (U + V) = c1 (W := W) hn U + c1 (W := W) hn V := by
  ext i j; rfl

theorem isTwoCochain_add (hn : W.rank + t = n) {a : ℕ} (U V : Mx D a n) :
    c2 (W := W) hn (U + V) = c2 (W := W) hn U + c2 (W := W) hn V := by
  ext i j; rfl

theorem first_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c1 (W := W) hn (jn hn x v) = x := by
  ext i j
  simp [c1, jn]

theorem second_columns_join_eq (hn : W.rank + t = n) {a : ℕ} (x : Mx D a W.rank) (v : Mx D a t) :
    c2 (W := W) hn (jn hn x v) = v := by
  ext i j
  simp [c2, jn]

theorem ww_mul_inv (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h b : GA D W) :
    ww W x₀ (h * b⁻¹) = mm (mt W b) (ww W x₀ h) := by
  simp only [ww, mm, mul_inv_rev, inv_inv, mt_mul, Matrix.mul_assoc]

theorem ac_zp (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {g : GA D B} {α : Mx D t t} {c : Mx D t W.rank} {b : GA D W}
    (h1 : mm (mt B g) d.jX = mm d.jX α) (h2 : mm (mt B g) d.j0 = mm d.jX c + mm d.j0 (mt W b)) (p : Par D n t W) :
    ac B g (zp d hn x₀ p) =
      zp d hn x₀ (p.1 * b⁻¹, mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0, p.2.2) := by
  have key : mm (mt B g) (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) =
      mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹)) := by
    rw [isOneCochain_add, C1_mul, first_columns_join_eq, ww_mul_inv]
    simp only [mm] at h1 h2 ⊢
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.add_mul, Matrix.mul_add]
    simp only [Matrix.mul_assoc]
    abel
  have key2 : mm (mt B g) (mm d.jX (c2 (W := W) hn p.2.1)) =
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) := by
    rw [isTwoCochain_add, mul_sub_one_mulVec_mem_spL, second_columns_join_eq]
    simp only [mm] at h1 ⊢
    rw [← Matrix.mul_assoc, h1, add_zero, Matrix.mul_assoc]
  unfold ac zp
  refine Prod.ext key ?_
  change mm (mt B g) (mm (mm d.jX (c1 (W := W) hn p.2.1) + mm d.j0 (ww W x₀ p.1)) p.2.2 + mm d.jX (c2 (W := W) hn p.2.1)) =
    mm (mm d.jX (c1 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0)) + mm d.j0 (ww W x₀ (p.1 * b⁻¹))) p.2.2 +
      mm d.jX (c2 (W := W) hn (mm α p.2.1 + jn hn (mm c (ww W x₀ p.1)) 0))
  rw [← key, ← key2]
  simp only [mm]
  rw [Matrix.mul_add, Matrix.mul_assoc]

theorem map_aff {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure]
    (φ : G ≃ₜ+ G) (s : G) : ν.map (fun U => φ U + s) = (addEquivAddHaarChar φ)⁻¹ • ν := by
  have h := addEquivAddHaarChar_smul_map ν φ
  have hne : addEquivAddHaarChar φ ≠ 0 := (addEquivAddHaarChar_pos φ).ne'
  have hm : ν.map φ = (addEquivAddHaarChar φ)⁻¹ • ν := by
    conv_rhs => rw [← h]
    rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
  have e : (fun U : G => φ U + s) = (fun U => U + s) ∘ φ := rfl
  have hφ : Measurable (φ : G → G) := φ.continuous.measurable
  rw [e, ← Measure.map_map (measurable_add_const s) hφ, hm, Measure.map_smul, map_add_right_eq_self]
  exact (measurable_add_const s).aemeasurable

theorem map_skew {H A Y : Type} [MeasurableSpace H] [MeasurableSpace A] [MeasurableSpace Y] {m : Measure H} {ν : Measure A}
    {μ : Measure Y} [SFinite m] [SFinite ν] [SFinite μ] {g : H → H} (hg : MeasurePreserving g m m) {f : H → A → A}
    (hf : Measurable (Function.uncurry f)) {c : ℝ≥0} (hc : ∀ h, ν.map (f h) = c • ν) :
    (m.prod (ν.prod μ)).map (fun p : H × A × Y => (g p.1, f p.1 p.2.1, p.2.2)) = c • m.prod (ν.prod μ) := by
  have hfm : ∀ h, Measurable (f h) := fun h => hf.of_uncurry_left
  have hs : Measurable (Function.uncurry fun (h : H) (z : A × Y) => ((f h z.1, z.2) : A × Y)) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd)
  have h1 : ∀ h, (ν.prod μ).map (fun z : A × Y => ((f h z.1, z.2) : A × Y)) = c • (ν.prod μ) := fun h => by
    have e := Measure.map_prod_map ν μ (hfm h) measurable_id
    rw [Measure.map_id, hc h] at e
    have e2 : (c • ν).prod μ = c • ν.prod μ := by
      have := Measure.prod_smul_left (μ := ν) (ν := μ) (c : ℝ≥0∞)
      exact this
    rw [e2] at e
    exact e.symm
  have h2 := (hg.skew_product hs (.of_forall h1)).map_eq
  rw [h2]
  exact Measure.prod_smul_right (μ := m) (ν := ν.prod μ) (c : ℝ≥0∞)

theorem map_left_add (a : GL (Fin t) (AE D)) (ν : Measure (Mx D t n)) (hν : ν.IsAddHaarMeasure) (s : Mx D t n) :
    ν.map (fun U => mm a.1 U + s) = ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) = absA D (Matrix.GeneralLinearGroup.det a) ^ n := by
    have := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n
      a (1 : GL (Fin n) (AE D))
    simpa using this
  have h := map_aff ν (GlobalTheory.ModuLR.lrCE a (1 : GL (Fin n) (AE D))) s
  rw [hc, ← inv_pow] at h
  rw [← h]
  congr 1
  funext U
  simp [GlobalTheory.ModuLR.lrCE_apply, mm]

theorem map_tau {d : HypDec B W t} (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure)
    (a : GL (Fin t) (AE D)) (b : GA D W) {S : GA D W → Mx D t n} (hS : Continuous S) :
    (Q0 I μ).map (fun p : Par D n t W => (p.1 * b, mm a.1 p.2.1 + S p.1, p.2.2)) =
      ((absA D (Matrix.GeneralLinearGroup.det a))⁻¹ ^ n : ℝ≥0) • Q0 I μ := by
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨g1, g2, g3, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hH := hf.1
  have hhaar := I.haar
  haveI := GlobalTheory.RegSch.Ibp.isMulRightInvariant I.m
  have hr : MeasurePreserving (fun h : GA D W => h * b) I.m I.m := measurePreserving_mul_right I.m b
  have hsm : Measurable (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) := by
    have : Continuous (Function.uncurry fun (h : GA D W) (U : Mx D t n) => mm a.1 U + S h) :=
      (continuous_const.matrix_mul continuous_snd).add (hS.comp continuous_fst)
    exact this.measurable
  exact map_skew hr hsm fun h => map_left_add a I.μ₁ hH (S h)

theorem continuous_S (hn : W.rank + t = n) (c : Mx D t W.rank) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun h : GA D W => jn hn (mm c (ww W x₀ h)) (0 : Mx D t t) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun h : GA D W => mm c (ww W x₀ h) := continuous_const.matrix_mul (continuous_ww x₀)
  refine continuous_matrix fun i j => ?_
  unfold jn
  simp only [Matrix.submatrix_apply, id]
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact hc.matrix_elem i k
  | inr k => exact continuous_const

theorem law : Law := by
  intro D n t B W d hn I μ hμ x₀ q
  subst hn
  obtain ⟨c, g, hcg⟩ := GlobalTheory.RegSch.IkStab.exists_valuation_adapted_index d q.2
  have h1 := GlobalTheory.RegSW.mul_jX d q
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨p1, p2⟩ := top_par (D := D) (W.rank + t) t W
  obtain ⟨-, -, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t (W.rank + t)
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have o0 : OpensMeasurableSpace (Par D (W.rank + t) t W) := p1.opensMeasurable
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have hS := continuous_S (W := W) (t := t) rfl c x₀
  have hac : Measurable (ac B (q : GA D B) (a := W.rank) (b := t)) :=
    ((continuous_ac B).comp (continuous_const.prodMk continuous_id)).measurable
  have hτ : Measurable fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    Continuous.measurable ((continuous_fst.mul continuous_const).prodMk
      (((continuous_const.matrix_mul (continuous_fst.comp continuous_snd)).add (hS.comp continuous_fst)).prodMk
        (continuous_snd.comp continuous_snd)))
  have e : (ac B (q : GA D B)) ∘ zp d rfl x₀ = zp d rfl x₀ ∘ fun p : Par D (W.rank + t) t W =>
      ((p.1 * g⁻¹, mm (GlobalTheory.RegSW.onX d q).1 p.2.1 + jn rfl (mm c (ww W x₀ p.1)) (0 : Mx D t t), p.2.2) : Par D (W.rank + t) t W) :=
    funext fun p => ac_zp d rfl x₀ h1 hcg p
  unfold rho
  rw [Measure.map_map hac (measurable_zp d rfl x₀), e, ← Measure.map_map (measurable_zp d rfl x₀) hτ,
    map_tau I μ hμ (GlobalTheory.RegSW.onX d q) g⁻¹ hS, Measure.map_smul]
  · rfl
  · exact (measurable_zp d rfl x₀).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting.LawPf

end
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ A x y = (fun i => σ (x i)) ⬝ᵥ (A *ᵥ y) := by
  have : hE σ A x y = ∑ i, ∑ j, σ (x i) * A i j * y j := rfl
  rw [this]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_normMat (σ : E →ₐ[F] E) {n : ℕ} (l ξ : Fin n → E) :
    hE σ (normMat σ l) ξ ξ = σ (l ⬝ᵥ ξ) * (l ⬝ᵥ ξ) := by
  have : hE σ (normMat σ l) ξ ξ = ∑ i, ∑ j, σ (ξ i) * (σ (l i) * l j) * ξ j := rfl
  rw [this]

  simp only [dotProduct, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dot_eq_zero_of_hE_normMat (σ : E →ₐ[F] E) {n : ℕ} {l ξ : Fin n → E}
    (h : hE σ (normMat σ l) ξ ξ = 0) : l ⬝ᵥ ξ = 0 := by
  rw [hE_normMat] at h
  rcases mul_eq_zero.1 h with h | h
  · exact (map_eq_zero_iff σ σ.toRingHom.injective).1 h
  · exact h

theorem hE_conj (σ : E →ₐ[F] E) {n : ℕ} (J P : Matrix (Fin n) (Fin n) E) (ξ : Fin n → E) :
    hE σ (cT (σ : E →+* E) P * J * P) ξ ξ = hE σ J (P *ᵥ ξ) (P *ᵥ ξ) := by
  rw [hE_eq_dot, hE_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (cT (σ : E →+* E) P)]
  congr 1
  ext j

  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, cT, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem anisoProj_mulVec (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E)
    (ξ : Fin n → E) (hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0) (hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0) :
    anisoProj σ J X Y *ᵥ ξ = ξ := by
  have h0 : ∀ k, projFam σ J X Y k *ᵥ ξ = 0 := by
    rintro (i | i)
    · simp only [projFam, Sum.elim_inl, lineProj, Matrix.vecMulVec_mulVec, hY i]
      ext k
      simp
    · simp only [projFam, Sum.elim_inr, lineProj, Matrix.vecMulVec_mulVec, hX i]
      ext k
      simp
  rw [anisoProj, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec, Finset.sum_eq_zero fun k _ => h0 k, sub_zero]

end GlobalTheory.CompanionTheory.ParCocompact.HermNondeg

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem hermFam_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ ξ : Fin n → E,
    (∀ j, hE σ (hermFam σ J X Y j) ξ ξ = 0) → ξ = 0 := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y hW ξ h
  have hY : ∀ i, rowOf σ J Y i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inl i)))
  have hX : ∀ i, rowOf σ J X i ⬝ᵥ ξ = 0 := fun i =>
    HermNondeg.dot_eq_zero_of_hE_normMat σ (h (some (Sum.inr i)))
  have hπ := HermNondeg.anisoProj_mulVec σ J X Y ξ hX hY
  have hn : hE σ J ξ ξ = 0 := by
    have := h none
    change hE σ (cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y) ξ ξ = 0 at this
    rwa [HermNondeg.hE_conj, hπ] at this
  refine hW.aniso ξ ?_ ?_ hn
  · ext i
    exact hX i
  · ext i
    exact hY i

end GlobalTheory.CompanionTheory.ParCocompact
end
end

section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.LeviComm

section Ring

variable {n r : ℕ} {R : Type} [CommRing R] {s : R →+* R} {Jm : Matrix (Fin n) (Fin n) R}
  {Xm Ym : Matrix (Fin n) (Fin r) R}

theorem pfr_swap (hF : PFr s Jm Xm Ym) : PFr s Jm Ym Xm :=
  ⟨hF.ss, hF.herm, hF.yy, hF.xx, hF.yx⟩

theorem row_mul {g : Matrix (Fin n) (Fin n) R} (hF : PFr s Jm Xm Ym) (hg : cT s g * Jm * g = Jm) {d d' : Fin r → R}
    (hX : g * Xm = Xm * diagonal d) (hY : g * Ym = Ym * diagonal d') :
    cT s Ym * Jm * g = diagonal d * (cT s Ym * Jm) := by
  have h1 : cT s (diagonal d') * diagonal d = 1 := by
    have e := pgram_unitary hg Ym Xm
    rw [hY, hX, hF.yx, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * diagonal d
        = cT s (diagonal d') * (cT s Ym * Jm * Xm) * diagonal d := by rw [hF.yx, Matrix.mul_one]
      _ = 1 := by rw [← e]; simp only [Matrix.mul_assoc]
  have h2 : diagonal d * cT s (diagonal d') = 1 := mul_eq_one_comm.1 h1
  have h3 : cT s (diagonal d') * (cT s Ym * Jm * g) = cT s Ym * Jm := by
    have e : cT s (g * Ym) * Jm * g = cT s Ym * Jm := by
      conv_rhs => rw [← hg]
      simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    rw [hY, Formalism.UG.cT_mul] at e
    calc cT s (diagonal d') * (cT s Ym * Jm * g) = cT s (diagonal d') * cT s Ym * Jm * g := by
          simp only [Matrix.mul_assoc]
      _ = cT s Ym * Jm := e
  calc cT s Ym * Jm * g = diagonal d * cT s (diagonal d') * (cT s Ym * Jm * g) := by rw [h2, Matrix.one_mul]
    _ = diagonal d * (cT s Ym * Jm) := by rw [Matrix.mul_assoc, h3]

theorem comm_vecMulVec {m : ℕ} {g : Matrix (Fin n) (Fin n) R} {C : Matrix (Fin n) (Fin m) R}
    {A : Matrix (Fin m) (Fin n) R} {d : Fin m → R} (hC : g * C = C * diagonal d) (hA : A * g = diagonal d * A)
    (i : Fin m) : g * vecMulVec (fun k => C k i) (A i) = vecMulVec (fun k => C k i) (A i) * g := by
  ext a b
  have e1 : ∑ k, g a k * C k i = C a i * d i := by
    have := congrFun (congrFun hC a) i
    rwa [Matrix.mul_apply, Matrix.mul_diagonal] at this
  have e2 : ∑ k, A i k * g k b = d i * A i b := by
    have := congrFun (congrFun hA i) b
    rwa [Matrix.mul_apply, Matrix.diagonal_mul] at this
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply]
  calc ∑ k, g a k * (C k i * A i b) = (∑ k, g a k * C k i) * A i b := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = C a i * (d i * A i b) := by rw [e1, mul_assoc]
    _ = C a i * ∑ k, A i k * g k b := by rw [e2]
    _ = ∑ k, C a i * A i k * g k b := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm

end Ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem lineProj_map (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) :
    (lineProj σ J C D i).map (inclR (F := F) (AF F)) =
      vecMulVec (fun k => adMat F C k i)
        (((cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) i) := by
  have e : (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) (adMat F D) : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) *
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (AF F) J : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) =
      (cT (σ : E →+* E) D * J).map (inclR (F := F) (AF F)) := by
    unfold JR
    rw [← cT_map_inclR, ← Matrix.map_mul]
  rw [e]
  ext a b
  exact map_mul (inclR (F := F) (AF F)) (C a i) ((cT (σ : E →+* E) D * J) i b)

theorem leviMin_comm_projFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (m) (hm : m ∈ leviMin σ J X Y) (k) :
    (matHom _ σ J m).1 * (projFam σ J X Y k).map (inclR (F := F) (AF F)) =
      (projFam σ J X Y k).map (inclR (F := F) (AF F)) * (matHom _ σ J m).1 := by
  obtain ⟨d, d', hX, hY⟩ := hm
  have hF := pfrA h hJ hW
  have hg := unitaryA_matHom m
  rcases k with i | i
  · simp only [projFam, Sum.elim_inl]
    rw [lineProj_map]
    exact comm_vecMulVec hX (row_mul hF hg hX hY) i
  · simp only [projFam, Sum.elim_inr]
    rw [lineProj_map]
    exact comm_vecMulVec hY (row_mul (pfr_swap hF) hg hY hX) i

end GlobalTheory.CompanionTheory.ParCocompact.LeviComm

end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.MuInertPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem delta_indep {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) : delta w μ Q₁ Q₂ = delta w μ' Q₁ Q₂ := by
  simp only [delta, hw, if_false]

theorem match_indep {n a b : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ) : Match n a b w μ f φ ↔ Match n a b w μ' f φ := by
  unfold Match
  simp only [delta_indep hw μ μ']

theorem muInert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  intro E _ _ _ n a b w hw μ μ' f φ
  exact match_indep hw μ μ' f φ

end GlobalTheory.CompanionTheory.MuInertPlace
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.leibniz_order_of_exact_sequences : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ResSeq k → PsiGP k → PhiGP k → PsiPG k → PhiPG k → PhiPG0 k → LeibnizOrd k := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | exact GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts <;> assumption)
end

section

open PositivityTheory.Rg.Rsw

theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  first | exact @GlobalTheory.CompanionTheory.RswPolar.polar | exact GlobalTheory.CompanionTheory.RswPolar.polar | (intros; apply GlobalTheory.CompanionTheory.RswPolar.polar <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.compact_adelic_norm_bounded : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact <;> assumption)
end
