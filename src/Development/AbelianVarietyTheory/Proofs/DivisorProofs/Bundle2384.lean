module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import ReciprocityTheory.SemistableReduction.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle012
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle016
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.SemistableReduction.SemiAll
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle025
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  first | exact @GlobalTheory.SmallElement.smallElement | exact GlobalTheory.SmallElement.smallElement | (intros; apply GlobalTheory.SmallElement.smallElement <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BalancedPointPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem conj_mem_iff (X : Data E r) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ ↔ σ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate σ)]
  simp [ComplexEmbedding.conjugate, star_star]

theorem sum_eq_two_mul (X : Data E r) (f : (E →+* ℂ) → ℝ)
    (hf : ∀ σ, f (ComplexEmbedding.conjugate σ) = f σ) :
    ∑ σ, f σ = 2 * ∑ τ : X.Ψ, f τ.1 := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]
  have h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      exact (conj_mem_iff X σ).2 hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).1 hσ
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; exact (hf σ).symm
  rw [h]; ring

theorem card_Ψ (X : Data E r) : (Fintype.card X.Ψ : ℝ) = fdeg E := by
  have h := sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Embeddings.card E ℂ] at h
  have h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ := by exact_mod_cast h
  rw [fdeg, h2, Nat.mul_div_cancel_left _ two_pos]

end

end GlobalTheory.BalancedPointPf

namespace GlobalTheory.BalancedPointPf

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem embVec_conj (σ : E →+* ℂ) (v : Fin r → E) :
    ReciprocityTheory.MultiplicativeHeights.embVec (ComplexEmbedding.conjugate σ) v = star (ReciprocityTheory.MultiplicativeHeights.embVec σ v) := by
  funext k
  simp [ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]

theorem maj_eq_hq (X : Data E r) (H : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r)
    (ho : IsOrth X x) (hH : ∀ τ : X.Ψ, (mat x τ)ᴴ * H τ.1 * mat x τ = 1) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = ReciprocityTheory.MultiplicativeHeights.hq (H τ.1) u := by
  have hmo := GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hmo.1 τ)
  have e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹ := by
    calc H τ.1 = (mat x τ * (mat x τ)⁻¹)ᴴ * H τ.1 * (mat x τ * (mat x τ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu]; simp
      _ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH τ, Matrix.mul_one]
  rw [hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]
  rfl

theorem balancedPoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  intro E _ _ _ r X
  obtain ⟨M, hss, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP
      ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have h0 : IsOrth X.toData x0 := fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)
  have hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u :=
    maj_eq_hq X.toData M.H x0 h0 hy2
  refine ⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩
  · intro N hN hlt
    have key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 →
        ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
      intro τ w hw
      obtain ⟨c, hc0, hc1, hc⟩ := hlt τ
      have h1 := hc w
      rw [hmaj, hmaj] at h1
      have hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := (M.posDef τ.1).re_dotProduct_pos hw
      have hc2 : c ^ 2 < 1 := by nlinarith
      nlinarith
    refine hNC N hN fun σ u hu => ?_
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩ u hu
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (conj_mem_iff X.toData σ).2 hσ
      have hsu : star u ≠ 0 := fun h => hu (by simpa using congrArg star h)
      have h := key ⟨_, hσ'⟩ (star u) hsu
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj] at h
  · intro v hv hv0
    classical
    set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef
    have hpos : ∀ σ, 0 < h σ := by
      intro σ
      refine (M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_
      funext k
      have := congrFun h0 k
      simp only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this
      exact this
    have hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ := by
      intro σ
      simp only [hhdef]
      rw [embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from
        M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]

    set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB
    have hrange : Set.range ![v] = {v} := by simp
    have hBL : B ≤ X.L' := by rw [hB, Submodule.span_le]; simpa using hv
    have hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v] := by
      refine ⟨fun i => ?_, ?_, fun y hy => ?_⟩
      · rw [Fin.eq_zero i]; exact Submodule.subset_span rfl
      · exact linearIndependent_unique_iff.2 (by simpa using hv0)
      · rw [hB, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hrange]
        have : (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E)) :=
          Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        rwa [algebraMap_smul] at this
    have hdeg := hss.2 B hBL 1 ![v] hbasis
    have hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1 := by
      rw [hrange, ← hB]; exact AddSubgroup.relIndex_self _
    have hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ := by
      intro σ
      rw [Matrix.det_unique]
      rfl
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg
    have hsum : 0 ≤ ∑ σ, Real.log (h σ) := by linarith
    rw [sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])] at hsum
    have hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1 := fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)
    have hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1) :=
      (by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_Ψ X.toData] at hsum2
    have e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1 := fun τ => hmaj τ _
    simp only [e]
    linarith

end GlobalTheory.BalancedPointPf
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteOpNorm

theorem span_colP {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ) (A : Matrix (Fin r) (Fin r) ℂ)
    (hA : (A * mat x τ).det ≠ 0) (w : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, w = ∑ a, K a • Matrix.mulVec A (X.colP x τ a) := by
  classical
  set M := A * mat x τ with hM
  set c := M⁻¹.mulVec w with hc
  have hw : w = M.mulVec c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec]
  refine ⟨fun a => c (Fin.castLE X.p0_le a), ?_⟩
  have hsum : ∀ f : Fin r → Fin r → ℂ,
      ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) = ∑ j : Fin r, f j := by
    intro f
    exact Fintype.sum_equiv (finCongr hp) _ _ (fun a => by congr 1)
  show w = ∑ a : Fin X.p0, (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j)) (Fin.castLE X.p0_le a)
  rw [hsum (fun j => c j • A.mulVec (ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j))]
  conv_lhs => rw [hw]
  funext k
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ReciprocityTheory.ChartRestriction.G.FD.col, hM, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem opNormLe_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, ∀ β : GL (Fin r) E,
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) = herm X.Gm v w) →
    ∀ τ : X.Ψ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x τ (β : Matrix (Fin r) (Fin r) E)
      (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro E _ _ _ r X hp x hx β hβ τ u
  set g : Matrix (Fin r) (Fin r) ℂ := (β : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' : Matrix (Fin r) (Fin r) ℂ := ((β⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg : g * g' = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hg'g : g' * g = 1 := by
    rw [hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one τ.1 τ.1.map_zero τ.1.map_one
  have hdetg : g.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetx : (mat x τ).det ≠ 0 := (hx τ).1
  have hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v :=
    GlobalTheory.MajInv.hermC_stab X hβ τ.1
  have H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP x τ a := by
    intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · obtain ⟨K, hK⟩ := span_colP X hp x τ 1 (by rw [Matrix.one_mul]; exact hdetx)
        (Matrix.mulVec g (X.colP x τ c))
      exact ⟨K, by simpa only [Matrix.one_mulVec] using hK⟩
  have H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP x τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c) := by
    intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · exact span_colP X hp x τ g (by rw [Matrix.det_mul]; exact mul_ne_zero hdetg hdetx) _
  have key : X.maj x τ (Matrix.mulVec g u) = X.maj x τ u := by
    have h := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_transfer X hx hx τ g g'
      (fun w => by rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]) hiso H1 H2 (Matrix.mulVec g u)
    rwa [Matrix.mulVec_mulVec, hg'g, Matrix.one_mulVec] at h
  rw [key]
  have h0 := ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ u
  have h1 : (1 : ℝ) ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    one_le_pow₀ (Real.one_le_exp (by positivity))
  nlinarith

end GlobalTheory.DefiniteOpNorm
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.LevDesc (move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_finite_order_levelMove_universalSemiAbelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) («γ» : LevelAut Dw l) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), 1 ≤ Dw.p + Dw.q → l.A = 1 → IsIso ρ → IsLevMove ρ ν (liftLa «γ») LinearMap.id → ∃ n : ℕ, 0 < n ∧ (fun f : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left => f ≫ ν.φ)^[n] (𝟙 _) = 𝟙 _ := by
  first | exact @GlobalTheory.MoveOrder.finite_order | exact GlobalTheory.MoveOrder.finite_order | (intros; apply GlobalTheory.MoveOrder.finite_order <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.exists_effective_QDivisor_offPoint_ampleClass : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  first | exact @GlobalTheory.exists_eff_off_pt_ample_class | exact GlobalTheory.exists_eff_off_pt_ample_class | (intros; apply GlobalTheory.exists_eff_off_pt_ample_class <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory.Cartier

namespace GlobalTheory.DenominatorExistenceLemmas

variable {M W : Scheme.{0}}

theorem finite_app (f : M ⟶ W) [IsProper f] [IsLocallyNoetherian W] {L : ReciprocityTheory.ChartRestriction.G.Semi.LB M}
    (hL : IsAmpleLB L) {V : W.Opens} (hV : IsAffineOpen V) : (f.app V).hom.Finite := by
  obtain ⟨_, hfa⟩ := GlobalTheory.ProperFinite.isFiniteQC_pushforward f hL (structureModule M)
  exact hfa V hV

variable [IsIntegral M] [IsIntegral W]


omit [IsIntegral W] in
theorem gen_mem_preimage (f : M ⟶ W) [IsDominant f] {U : W.Opens} {y : W} (hy : y ∈ U) :
    genericPoint M ∈ f ⁻¹ᵁ U := by
  obtain ⟨m, hm⟩ := f.denseRange.exists_mem_open U.isOpen ⟨y, hy⟩
  exact gen_mem (U := f ⁻¹ᵁ U) (x := m) hm


omit [IsIntegral W] in
theorem fnOf_map {U V : M.Opens} (e : V ≤ U) (h : genericPoint M ∈ V) (a : Γ(M, U)) :
    fnOf V h (M.presheaf.map (homOfLE e).op a) = fnOf U (e h) a := by
  exact fnOf_resG e h a

theorem exists_denominator {V : W.Opens} (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) {ι : Type} [Finite ι]
    (c : ι → W.functionField) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ i, ∃ a : Γ(W, V), fnOf V hg a = fnOf V hg d * c i := by
  have : Nonempty V := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen W V hV
  obtain ⟨⟨d, hd⟩, hdc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors Γ(W, V)) c
  refine ⟨d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hdc i
  refine ⟨a, ?_⟩
  rw [Algebra.smul_def] at ha
  exact ha

theorem exists_denominator_all (f : M ⟶ W) [IsDominant f] {V : W.Opens} (hV : IsAffineOpen V)
    (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) (hf : (f.app V).hom.Finite) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) :
    ∃ d : Γ(W, V), fnOf V hg d ≠ 0 ∧ ∀ j (b : Γ(M, f ⁻¹ᵁ V)), ∃ a : Γ(W, V),
      fnOf V hg a = fnOf V hg d * co j (fnOf (f ⁻¹ᵁ V) hg' b) := by
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(W, V) Γ(M, f ⁻¹ᵁ V) := hf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Γ(W, V)) (M := Γ(M, f ⁻¹ᵁ V))
  obtain ⟨d, hd0, hd⟩ := exists_denominator hV hg
    (fun p : Fin r × Fin n => co p.1 (fnOf (f ⁻¹ᵁ V) hg' (s p.2)))
  refine ⟨d, hd0, fun j b => ?_⟩
  have hb : b ∈ Submodule.span Γ(W, V) (Set.range s) := hs ▸ Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact hd (j, k)
  | zero => exact ⟨0, by simp only [map_zero, mul_zero]⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hx'
    exact ⟨a + a', by rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, ha', mul_add]⟩
  | smul t x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨t * a, ?_⟩
    have ht : fnOf (f ⁻¹ᵁ V) hg' (t • x) = functionFieldMap f (fnOf V hg t) * fnOf (f ⁻¹ᵁ V) hg' x := by
      rw [Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra]
      congr 1
      exact GlobalTheory.Cartier.DomPull.fnOf_app f hg' t
    rw [ht, hco, map_mul, ha]
    ring

theorem exists_pow_mul_eq (f : M ⟶ W) [IsDominant f] [QuasiCompact f] [QuasiSeparatedSpace M] {V : W.Opens}
    (hV : IsAffineOpen V) (hg : genericPoint W ∈ V) (hg' : genericPoint M ∈ f ⁻¹ᵁ V) {y : W} (hy : y ∈ V)
    {V' : W.Opens} (hy' : y ∈ V') (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) :
    ∃ (u : W.functionField) (b : Γ(M, f ⁻¹ᵁ V)), UnitAt y u ∧
      fnOf (f ⁻¹ᵁ V) hg' b = functionFieldMap f u * fnOf (f ⁻¹ᵁ V') h z := by
  obtain ⟨g, hgV', hyg⟩ := hV.exists_basicOpen_le ⟨y, hy'⟩ hy
  have hle : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V' := by
    rw [← Scheme.preimage_basicOpen]
    exact fun x hx => hgV' hx
  have hgb : genericPoint M ∈ M.basicOpen (f.app V g) := by
    rw [← Scheme.preimage_basicOpen]
    exact gen_mem_preimage f hyg
  obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated M (f ⁻¹ᵁ V)
    (f.isCompact_preimage hV.isCompact) (IsQuasiSeparated.of_quasiSeparatedSpace _) (f.app V g) (M.presheaf.map (homOfLE hle).op z)
  have e0 : M.basicOpen (f.app V g) ≤ f ⁻¹ᵁ V := M.basicOpen_le _
  have h1 : fnOf _ hgb (M.presheaf.map (homOfLE e0).op b) =
      fnOf _ hgb (M.presheaf.map (homOfLE e0).op (f.app V g)) ^ n *
        fnOf _ hgb (M.presheaf.map (homOfLE hle).op z) := by
    rw [← map_pow, ← map_mul]
    exact congrArg _ hb
  rw [fnOf_map, fnOf_map, fnOf_map] at h1
  refine ⟨fnOf V hg g ^ n, b, ?_, ?_⟩
  · have hu : UnitAt y (fnOf V hg g) := (unitAt_fnOf_iff hy hg g).2 hyg
    clear h1 hb
    induction n with
    | zero => simpa using unitAt_one y
    | succ n ih => rw [pow_succ]; exact ih.mul hu
  · rw [map_pow, ← GlobalTheory.Cartier.DomPull.fnOf_app f hg' g]
    exact h1


omit [IsIntegral M] [IsIntegral W] in
theorem exists_local_denominator (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    [IsProper f] [IsLocallyNoetherian W] (L : ReciprocityTheory.ChartRestriction.G.Semi.LB M) (hL : IsAmpleLB L) {r : ℕ}
    (co : Fin r → M.functionField →+ W.functionField)
    (hco : ∀ j c x, co j (functionFieldMap f c * x) = c * co j x) (y : W) :
    ∃ (V : W.Opens) (hy : y ∈ V) (d : Γ(W, V)), fnOf V (gen_mem hy) d ≠ 0 ∧
      ∀ y' ∈ V, ∀ V' : W.Opens, y' ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r),
        RegAt y' (fnOf V (gen_mem hy) d * co j (fnOf (f ⁻¹ᵁ V') h z)) := by
  obtain ⟨V, hVa, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian f
  have : TopologicalSpace.NoetherianSpace M := GlobalTheory.IsAmpleLB.noetherianSpace hL
  have hg' : genericPoint M ∈ f ⁻¹ᵁ V := gen_mem_preimage f hyV
  obtain ⟨d, hd0, hd⟩ := exists_denominator_all f hVa (gen_mem hyV) hg' (finite_app f hL hVa) co hco
  refine ⟨V, hyV, d, hd0, fun y' hy'V V' hy'V' h z j => ?_⟩
  obtain ⟨u, b, hu, hb⟩ := exists_pow_mul_eq f hVa (gen_mem hyV) hg' hy'V hy'V' h z
  obtain ⟨a, ha⟩ := hd j b
  have hz : fnOf (f ⁻¹ᵁ V') h z = functionFieldMap f u⁻¹ * fnOf (f ⁻¹ᵁ V) hg' b := by
    rw [hb, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu.ne_zero, map_one, one_mul]
  rw [hz, hco, mul_left_comm (fnOf V (gen_mem hyV) d), ← ha]
  exact hu.inv.regAt.mul (regAt_fnOf hy'V _ a)

end GlobalTheory.DenominatorExistenceLemmas
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  first | exact @GlobalTheory.CechPer.eq_zero_of_isPer_zero | exact GlobalTheory.CechPer.eq_zero_of_isPer_zero | (intros; apply GlobalTheory.CechPer.eq_zero_of_isPer_zero <;> assumption)
end
