module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle027
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefCont

theorem continuous_coefR : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  intro D θ hθ V S M v a
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  unfold coefR
  refine continuous_finsetProd _ fun τ _ => ?_

  have hc : Continuous fun g : GA D V => cmp θ τ g := GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)
  have hu : ∀ g : GA D V, (cmp θ τ g)ᴴ * gramAt D V τ * cmp θ τ g = gramAt D V τ := by
    intro g
    have h0 := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram (tauE D τ)
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x) (θ τ) (hθ τ) g
    have he : (cmp θ τ g)ᴴ = ((cmp θ τ g).map (starRingEnd ℂ)).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he]
    exact h0
  have hB : M.fr τ * (M.fr τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hmem : ∀ g : GA D V, Formalism.REAL.inUJ (M.ε τ) (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) := by
    intro g
    unfold Formalism.REAL.inUJ
    calc (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)
        = ((M.fr τ)⁻¹)ᴴ * ((cmp θ τ g)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * cmp θ τ g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
          rw [M.fr_gram τ, hu g]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) := by
          rw [hB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hconj : Continuous fun g : GA D V => M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have hσ := (M.ds τ).2.2.1.2.2 (a τ)
  have hrep : Continuous fun g : GA D V => M.rep τ (cmp θ τ g) (a τ) :=
    hσ.comp_continuous hconj hmem
  exact continuous_const.inner hrep

end GlobalTheory.SepPer.CoefCont
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepPer.MajDom

theorem re_form_le {n : ℕ} (G fr : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool)
    (h : frᴴ * Formalism.REAL.Jm ε * fr = G) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (G *ᵥ v)).re ≤ ∑ i, ‖(fr *ᵥ v) i‖ ^ 2 := by
  subst h
  have e : star v ⬝ᵥ ((frᴴ * Formalism.REAL.Jm ε * fr) *ᵥ v) =
      star (fr *ᵥ v) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (fr *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have hd : ∀ w : Fin n → ℂ, Formalism.REAL.Jm ε *ᵥ w = fun i => (if ε i = true then (1 : ℂ) else -1) * w i := by
    intro w; funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [e, hd, dotProduct, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hw : star (fr *ᵥ v) i * ((if ε i = true then (1 : ℂ) else -1) * (fr *ᵥ v) i) =
      (if ε i = true then (1 : ℂ) else -1) * ((‖(fr *ᵥ v) i‖ : ℂ) ^ 2) := by
    rw [← Complex.conj_mul', Pi.star_apply, Complex.star_def]
    ring
  rw [hw]
  split_ifs
  · simp only [one_mul]
    norm_cast
  · have : (-((‖(fr *ᵥ v) i‖ : ℂ) ^ 2)).re = -(‖(fr *ᵥ v) i‖ ^ 2) := by norm_cast
    rw [neg_one_mul, this]
    nlinarith [sq_nonneg ‖(fr *ᵥ v) i‖]

theorem form_isom {n : ℕ} (G P : Matrix (Fin n) (Fin n) ℂ) (hP : Pᴴ * G * P = G) (u : Fin n → ℂ) :
    star (P *ᵥ u) ⬝ᵥ (G *ᵥ (P *ᵥ u)) = star u ⬝ᵥ (G *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP]

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

variable {D : D7}

theorem tauE_sig (τ : D.what₂.Tau) (a : D.host.E) :
    tauE D τ (D.sp.cm.sig a) = starRingEnd ℂ (tauE D τ a) :=
  D.sp.cm.cmUnram.2.1 _ a

theorem cmp_mulVec (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (γ : GA D V) (z₀ z : Fin V.rank → D.host.E)
    (h : mt V γ *ᵥ ratV z₀ = ratV z) (τ : D.what₂.Tau) :
    cmp θ τ γ *ᵥ (fun i => tauE D τ (z₀ i)) = fun i => tauE D τ (z i) := by
  let φ : AE D →+* ℂ := (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hφ : ∀ e : D.host.E, φ (incA D e) = tauE D τ e := by
    intro e
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 ⊗ₜ e)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    exact (hθ τ).1 e
  have hc : cmp θ τ γ = (mt V γ).map φ := rfl
  have e1 : (⇑φ ∘ ratV z₀) = fun j => tauE D τ (z₀ j) := funext fun j => hφ (z₀ j)
  funext i
  have := congrArg (fun w => φ (w i)) h
  simp only [RingHom.map_mulVec] at this
  rw [e1] at this
  rw [hc, this]
  exact hφ (z i)

theorem form_zv {Y V : HSp D} (d : HermitianOrthogonalExtensionData Y V 1 1) (τ : D.what₂.Tau) :
    star (fun i => tauE D τ (zv d i)) ⬝ᵥ (gramAt D V τ *ᵥ fun i => tauE D τ (zv d i)) = 1 := by
  have hg := congrArg (fun M => tauE D τ (M 0 0)) d.gram

  simp only [antiDiagonalSignGramMatrix, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
  tauE_sig] at hg
  simp only [dotProduct, Matrix.mulVec, gramAt, Matrix.map_apply, Pi.star_apply, Complex.star_def, Finset.mul_sum, zv]
  refine Eq.trans ?_ (hg.trans (by simp))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  congr 1
  exact (tauE_sig τ _).symm

end GlobalTheory.SepPer.MajDom

namespace GlobalTheory.SepPer.MajDom

theorem one_le_nrm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (B : Fr V) (x : GA D Y)
    (γ : GA D V) (z : Fin V.rank → D.host.E), γ ∈ GQ V → mt V γ *ᵥ ratV (zv d) = ratV z →
    ∀ τ, 1 ≤ nrm θ B (stabilizerEmbedding d x) τ z := by
  intro D θ hθ Y V d B x γ z _ hmt τ
  set G := gramAt D V τ
  set u₀ : Fin V.rank → ℂ := fun i => tauE D τ (zv d i) with hu₀
  set P := cmp θ τ (stabilizerEmbedding d x)⁻¹ * cmp θ τ γ with hP
  have hv : cmp θ τ (stabilizerEmbedding d x)⁻¹ *ᵥ (fun i => tauE D τ (z i)) = P *ᵥ u₀ := by
    rw [← cmp_mulVec θ hθ γ (zv d) z hmt τ, Matrix.mulVec_mulVec]
  have hPG : Pᴴ * G * P = G := by
    have h1 := GlobalTheory.Doubling.infMat_isometry hθ τ (stabilizerEmbedding d x)⁻¹
    have h2 := GlobalTheory.Doubling.infMat_isometry hθ τ γ
    calc Pᴴ * G * P = (cmp θ τ γ)ᴴ * ((cmp θ τ (stabilizerEmbedding d x)⁻¹)ᴴ * G * cmp θ τ (stabilizerEmbedding d x)⁻¹) * cmp θ τ γ := by
          rw [hP, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]
  have hform : star (P *ᵥ u₀) ⬝ᵥ (G *ᵥ (P *ᵥ u₀)) = 1 := by
    rw [form_isom G P hPG u₀]
    exact form_zv d τ
  have key := re_form_le G (B.fr τ) (B.ε τ) (B.fr_gram τ) (P *ᵥ u₀)
  rw [hform, Complex.one_re] at key
  unfold nrm eu
  rw [hv]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt key

end GlobalTheory.SepPer.MajDom
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

variable {D : D7}

def compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) :
    (Fin V.rank → D.host.E) →+ (D.what₂.Tau → EuclideanSpace ℂ (Fin V.rank)) where
  toFun w τ := WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (w i)))
  map_zero' := by
    funext τ
    have h : (fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i)) = 0 := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((0 : Fin V.rank → D.host.E) i))) = 0
    rw [h, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rfl
  map_add' x y := by
    funext τ
    have h : (fun i => tauE D τ ((x + y) i)) = (fun i => tauE D τ (x i)) + fun i => tauE D τ (y i) := by
      funext i; simp
    show WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ ((x + y) i))) =
      WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (x i))) +
        WithLp.toLp 2 (B.fr τ *ᵥ (cmp θ τ g⁻¹ *ᵥ fun i => tauE D τ (y i)))
    rw [h, Matrix.mulVec_add, Matrix.mulVec_add, WithLp.toLp_add]

theorem norm_compVec (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (w : Fin V.rank → D.host.E) (τ : D.what₂.Tau) :
    ‖compVec θ V B g w τ‖ = nrm θ B g τ w := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem latSum_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (B : Fr V) (g : GA D V) (L : Lat V) (R : ℝ), 1 ≤ V.rank → 1 < R → (∀ w ∈ L, w ≠ 0 → R ≤ ∏ τ, nrm θ B g τ w) → ∀ s : Finset (Fin V.rank → D.host.E), (∀ w ∈ s, w ∈ L ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + nrm θ B g τ w) / 3) ^ (2 * V.rank + 5))⁻¹ ≤ Real.exp ((6 * (V.rank : ℝ) + 9) * Fintype.card D.what₂.Tau) / R := by
  intro D θ V B g L R hn hR hL s hs
  classical
  have hnorm : ∀ w τ, ‖compVec θ V B g w τ‖ = nrm θ B g τ w := norm_compVec θ V B g
  by_cases hι : IsEmpty D.what₂.Tau
  · have hs0 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [Finset.univ_eq_empty, Finset.prod_empty] at h1
      linarith
    subst hs0
    rw [Finset.sum_empty]
    exact div_nonneg (Real.exp_pos _).le (by linarith)
  · haveI : Nonempty D.what₂.Tau := not_isEmpty_iff.mp hι
    have hzero : ∀ w, compVec θ V B g w = 0 → ∏ τ, nrm θ B g τ w = 0 := by
      intro w h0
      refine Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary _)) ?_
      rw [← hnorm, h0, Pi.zero_apply, norm_zero]
    have hinj : Set.InjOn (compVec θ V B g) (s : Set _) := by
      intro x hx y hy hxy
      by_contra hne
      have hm : x - y ∈ L := L.sub_mem (hs x hx).1 (hs y hy).1
      have h1 := hL _ hm (sub_ne_zero.mpr hne)
      have hz : compVec θ V B g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      rw [hzero _ hz] at h1
      linarith
    have key := GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound D.what₂.Tau V.rank (L.toAddSubgroup.map (compVec θ V B g)) R hn hR ?_
      (s.image (compVec θ V B g)) ?_
    · rw [Finset.sum_image hinj] at key
      simpa only [hnorm] using key
    · intro v hv hv0
      obtain ⟨w, hwL, rfl⟩ := AddSubgroup.mem_map.mp hv
      have hwL' : w ∈ L := hwL
      have hw0 : w ≠ 0 := by rintro rfl; exact hv0 (map_zero _)
      simpa only [hnorm] using hL w hwL' hw0
    · intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      refine ⟨AddSubgroup.mem_map_of_mem _ (hs w hw).1, ?_⟩
      intro h0
      have h1 := hL w (hs w hw).1 (hs w hw).2
      rw [hzero w h0] at h1
      linarith

end GlobalTheory.SepPer

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.TermDeriv

theorem hasDerivAt_coef_oneP : ∀ (D : D7), GlobalTheory.Published.HarishChandraModules → ∀ (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v b : ∀ τ, M.H τ) (τ : D.what₂.Tau), b τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ → ∀ X ∈ lieAt V τ, ∀ x : GA D V, HasDerivAt (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) (coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x) 0 := by
  intro D hHC θ hθ V S M K v b τ hb X hX x
  have hfin : ∀ s : ℝ, Lev.finE V (x * oneP θ V τ X s) = Lev.finE V x := by
    intro s
    have h : finHom V (oneP θ V τ X s) = 1 := GlobalTheory.PointAtPlaceHom.atTau_mem V τ _
    show (Formalism.UG.bc (Lev.swapAE D)).comp (finHom V) (x * oneP θ V τ X s) = _
    rw [map_mul, MonoidHom.comp_apply (Formalism.UG.bc (Lev.swapAE D)) (finHom V) (oneP θ V τ X s), h, map_one, mul_one]
    rfl
  by_cases hK : Lev.finE V x ∈ K
  swap
  · have e : (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun _ => 0 := by
      funext s
      simp only [coef, hfin s, hK, if_false]
    rw [e]
    have e2 : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x = 0 := by
      simp only [coef, hK, if_false]
    rw [e2]
    exact hasDerivAt_const _ _
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  have hsv : SmoothVec (lieAt V τ) (M.rep τ) (b τ) :=
    hHC.smoothVec hstd.1 hstd.2.1 hb (M.fr_unit τ) (M.fr_gram τ)
  have hd0 := Formalism.IndefR.SchurOrthogonalityAlt.gp_sv_hasDerivAt hsv hX 0
  rw [zero_smul, NormedSpace.exp_zero, Formalism.IndefR.SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] at hd0
  set c : ℂ := ∏ τ' ∈ Finset.univ.erase τ, ⟪v τ', M.rep τ' (cmp θ τ' x) (b τ')⟫_ℂ with hc
  have hfun : ∀ s : ℝ, coef θ M K v b (x * oneP θ V τ X s) =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ := by
    intro s
    simp only [coef, hfin s, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
    congr 1
    · refine Finset.prod_congr rfl fun τ' hτ' => ?_
      have hne := Finset.ne_of_mem_erase hτ'
      have h := (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.2 τ' hne
      show ⟪v τ', M.rep τ' (infMat D.sp.cm.sig V.gram (θ τ') (x * oneP θ V τ X s)) (b τ')⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, h, Matrix.mul_one]
    · show ⟪v τ, M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (x * oneP θ V τ X s)) (b τ)⟫_ℂ = _
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul, (GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s).2.1,
        Formalism.IndefR.SchurOrthogonalityAlt.rep_mul M τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ) (GlobalTheory.Mem.Lift.exp_mem hX s)]
      rfl
  have hval : coef θ M K v (Function.update b τ (dRep (M.rep τ) X (b τ))) x =
      c * ⟪v τ, M.rep τ (cmp θ τ x) (dRep (M.rep τ) X (b τ))⟫_ℂ := by
    simp only [coef, hK, if_true, coefR]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ τ), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun τ' hτ' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ')]
  rw [hval, show (fun s : ℝ => coef θ M K v b (x * oneP θ V τ X s)) = fun s : ℝ =>
      c * ⟪v τ, M.rep τ (cmp θ τ x) (M.rep τ (NormedSpace.exp (s • X)) (b τ))⟫_ℂ from funext hfun]
  refine HasDerivAt.const_mul c ?_
  exact (((innerSL ℂ (v τ)).comp (M.rep τ (cmp θ τ x))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd0

end GlobalTheory.TermDeriv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    exact (Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ ⟨hlat, hdual⟩).span_eq_top
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hspan
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add (f := _), ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
end
