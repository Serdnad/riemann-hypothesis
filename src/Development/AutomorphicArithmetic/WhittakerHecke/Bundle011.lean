module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle020
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RapidDecay
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.GlobalFields.Adele.Topology
public import Development.AutomorphicArithmetic.WhittakerHecke.BlockDiagonalEqLeviEmbedding
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
open GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {r s : ℕ}

private theorem lev_entry_le {F : Type*} [NormedField F] (ev : Ad E →+* F) (a : GA E r) (A : GL (Fin r) F)
    (hA : ∀ i j, (A : Matrix (Fin r) (Fin r) F) i j = ev ((a : Matrix (Fin r) (Fin r) (Ad E)) i j)) (i j : Fin (r + s)) :
    ‖ev (((lev (Ad E) r s (a, 1) : GL (Fin (r + s)) (Ad E)) : Matrix (Fin (r + s)) (Fin (r + s)) (Ad E)) i j)‖ ≤ locHeight A := by
  rw [GlobalTheory.SmGL.val_emb₂]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  have h0 : (0 : ℝ) ≤ locHeight A := (locHeight_pos A).le
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simpa [hA] using norm_apply_le_locHeight A i' j'
  · simpa using h0
  · simpa using h0
  · by_cases h : i' = j'
    · subst h
      simpa using one_le_locHeight A
    · simpa [Matrix.one_apply_ne h] using h0

private theorem lev_inv (a : GA E r) : (lev (Ad E) r s (a, 1))⁻¹ = lev (Ad E) r s (a⁻¹, 1) := by
  rw [← map_inv, Prod.inv_mk, inv_one]

private theorem locHeight_inf_le (w : InfinitePlace E) (a : GA E r) :
    locHeight (infAt w (lev (Ad E) r s (a, 1))) ≤ locHeight (infAt w a) := by
  refine locHeight_le (one_le_locHeight _) (fun i j => lev_entry_le (infEval w) a _ (fun _ _ => rfl) i j) fun i j => ?_
  rw [← infAt_inv, lev_inv, ← locHeight_inv (infAt w a), ← infAt_inv]
  exact lev_entry_le (infEval w) a⁻¹ _ (fun _ _ => rfl) i j

private theorem locHeight_fin_le (v : HeightOneSpectrum (𝓞 E)) (a : GA E r) :
    locHeight (finAt v (lev (Ad E) r s (a, 1))) ≤ locHeight (finAt v a) := by
  refine locHeight_le (one_le_locHeight _) (fun i j => lev_entry_le (finEval v) a _ (fun _ _ => rfl) i j) fun i j => ?_
  rw [← finAt_inv, lev_inv, ← locHeight_inv (finAt v a), ← finAt_inv]
  exact lev_entry_le (finEval v) a⁻¹ _ (fun _ _ => rfl) i j

private theorem height_lev_le (s : ℕ) (a : GA E r) : AutomorphicForm.height (lev (Ad E) r s (a, 1)) ≤ AutomorphicForm.height a := by
  classical
  set x : GA E (r + s) := lev (Ad E) r s (a, 1) with hx
  set t := (finite_mulSupport_locHeight_finAt x).union (finite_mulSupport_locHeight_finAt a)
  have e1 : ∏ᶠ v : HeightOneSpectrum (𝓞 E), locHeight (finAt v x) = ∏ v ∈ t.toFinset, locHeight (finAt v x) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inl hv
  have e2 : ∏ᶠ v : HeightOneSpectrum (𝓞 E), locHeight (finAt v a) = ∏ v ∈ t.toFinset, locHeight (finAt v a) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inr hv
  unfold AutomorphicForm.height
  refine mul_le_mul ?_ ?_ (le_trans zero_le_one (one_le_finprod_locHeight _)) (le_trans zero_le_one (one_le_prod_locHeight _))
  · exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (locHeight_pos _).le _)
      fun w _ => pow_le_pow_left₀ (locHeight_pos _).le (locHeight_inf_le w a) _
  · rw [e1, e2]
    exact Finset.prod_le_prod₀ (fun v _ => (locHeight_pos _).le) fun v _ => locHeight_fin_le v a

private theorem ct_growth {n : ℕ} (r : ℕ) (φ : GA E n → ℂ) {B : ℝ} {N : ℕ} (hφ : ∀ g, ‖φ g‖ ≤ B * AutomorphicForm.height g ^ N) :
    ∃ C : ℝ, ∀ g, ‖constantTerm r φ g‖ ≤ C * AutomorphicForm.height g ^ N := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hC.image (continuous_unipGL (K := E) (n := n) (r := r)))
  have hc : 1 ≤ heightConst E n := one_le_heightConst
  have hμ : unipMeasure E n r (unipFundamentalDomain E n r) < ⊤ := (measure_mono hDC).trans_lt hC.measure_lt_top
  refine ⟨|B| * (heightConst E n * max M 1) ^ N * (unipMeasure E n r).real (unipFundamentalDomain E n r), fun g => ?_⟩
  have hg := height_pos g
  have hb : ∀ X ∈ unipFundamentalDomain E n r, ‖φ (unipGL X * g)‖ ≤ |B| * (heightConst E n * max M 1) ^ N * AutomorphicForm.height g ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst E n * max M 1 * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((hM _ ⟨X, hDC hX, rfl⟩).trans (le_max_left _ _)) (by linarith)) hg.le)
    refine (hφ _).trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (height_pos _).le _)).trans ?_)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h1 _) (abs_nonneg _)
  have := norm_setIntegral_le_of_norm_le_const hμ hb
  refine this.trans_eq ?_
  ring

end

theorem UpperTheory.integrable_constantTerm_leviEmbedding_mul_conj_cuspForm :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (Pl E)) (r s : ℕ) (b : Blo S r) (φ : Sm E (r + s)), Umg φ → ∀ (g : GA E r) (m : GA E s),
      Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g, m)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) := by
  intro E _ _ _ S r s b φ hφ g m
  obtain ⟨F, hF, -, hFl, -⟩ := UpperTheory.ConvolutionTheory.BW.ctOps E r s φ hφ
  have hcφ : Continuous φ.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E (r + s)).2 φ hφ).1
  obtain ⟨hfU, hfC⟩ := UpperTheory.ConvolutionTheory.BW.cuspUmg E r b.f b.cusp
  have hcf : Continuous b.f.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E r).2 b.f hfU).1
  obtain ⟨N, hN⟩ := hφ.growth
  obtain ⟨B, hB⟩ := hN 1
  have hB' : ∀ g, ‖φ.1 g‖ ≤ B * AutomorphicForm.height g ^ N := fun g => by
    simpa using hB g
  obtain ⟨C, hC⟩ := ct_growth r φ.1 hB'
  obtain ⟨D, hD⟩ := UpperTheory.ConvolutionTheory.BW.rapidDecay E r b.f hfU hfC N
  let H : GA E r → ℂ := fun x =>
    AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * g, m)) * starRingEnd ℂ (b.f.1 x)
  have hct : ∀ (γ : GL (Fin r) E) (x : GA E r),
      AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (ratGL E r γ * x * g, m)) =
        AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * g, m)) := fun γ x => by
    have e : lev (Ad E) r s (ratGL E r γ * x * g, m) =
        lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (x * g, m) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul, mul_assoc]
    rw [← hF, e]
    exact hFl (γ, 1) _
  have hHl : AutomorphicForm.IsLeftInvariant H := fun γ x => by
    change AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (ratGL E r γ * x * g, m)) *
      starRingEnd ℂ (b.f.1 (ratGL E r γ * x)) = _
    rw [hct]
    exact congrArg _ (congrArg _ (hfU.left γ x))
  have hHc : Continuous H := by
    refine ((UpperTheory.continuous_constantTerm E (r + s) r φ.1 hcφ).comp ?_).mul (Complex.continuous_conj.comp hcf)
    exact ((GlobalTheory.SmGL.continuous_leviEmb (Ad E) _).comp (GlobalTheory.SmGL.continuous_leviTwo (Ad E))).comp ((continuous_id.mul continuous_const).prodMk continuous_const)
  set L := AutomorphicForm.height (lev (Ad E) r s (g, m)) with hL
  have hL0 : 0 < L := AutomorphicForm.height_pos _
  have hc0 : 0 < AutomorphicForm.heightConst E (r + s) := one_pos.trans_le AutomorphicForm.one_le_heightConst
  have hbound : ∀ y : normOneGL (K := E) (n := r), ‖H (y : GA E r)‖ ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * D := by
    intro y
    have hq1 : 1 ≤ PositivityTheory.Rg.Tf.Core.qht y := le_ciInf fun γ => AutomorphicForm.one_le_height _
    obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (show PositivityTheory.Rg.Tf.Core.qht y < 2 * PositivityTheory.Rg.Tf.Core.qht y by linarith)
    obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have hγ'' : ((γ : normOneGL (K := E) (n := r)) : GA E r) = ratGL E r γ' := hγ'.symm
    set y' : GA E r := ratGL E r γ' * (y : GA E r) with hy'
    have hy'h : AutomorphicForm.height y' < 2 * PositivityTheory.Rg.Tf.Core.qht y := by
      rw [hy', ← hγ'']; exact hγ
    have e1 : H (y : GA E r) = H y' := (hHl γ' _).symm
    have e2 : ‖b.f.1 y'‖ = ‖b.f.1 (y : GA E r)‖ := congrArg _ (hfU.left γ' _)
    have h3 : AutomorphicForm.height (lev (Ad E) r s (y' * g, m)) ≤
        2 * AutomorphicForm.heightConst E (r + s) * L * PositivityTheory.Rg.Tf.Core.qht y := by
      have e : lev (Ad E) r s (y' * g, m) = lev (Ad E) r s (y', 1) * lev (Ad E) r s (g, m) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      rw [e]
      refine (AutomorphicForm.height_mul_le _ _).trans ?_
      have h4 := (height_lev_le s y').trans hy'h.le
      calc _ ≤ AutomorphicForm.heightConst E (r + s) * (2 * PositivityTheory.Rg.Tf.Core.qht y) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hc0.le) hL0.le
        _ = _ := by ring
    have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht y := by linarith
    have h5 : ‖AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (y' * g, m))‖ ≤
        |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * PositivityTheory.Rg.Tf.Core.qht y ^ N := by
      refine (hC _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (AutomorphicForm.height_pos _).le _)).trans ?_)
      calc _ ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L * PositivityTheory.Rg.Tf.Core.qht y) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h3 _) (abs_nonneg _)
        _ = _ := by rw [mul_pow]; ring
    have hK : 0 ≤ |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N := by positivity
    rw [e1]
    change ‖_ * _‖ ≤ _
    rw [norm_mul, RCLike.norm_conj, e2]
    calc _ ≤ (|C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * PositivityTheory.Rg.Tf.Core.qht y ^ N) * ‖b.f.1 (y : GA E r)‖ :=
          mul_le_mul_of_nonneg_right h5 (norm_nonneg _)
      _ = |C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * (‖b.f.1 (y : GA E r)‖ * PositivityTheory.Rg.Tf.Core.qht y ^ N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hD y) hK
  have := isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  have he : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g, m)) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) =
      CuspidalSpectrum.cuspQuot hHl := funext fun y => by
    have h := CuspidalSpectrum.cuspQuot_mk hHl (Quotient.out y)
    rw [show RightCosetSpace.mk (rationalGLOne (K := E) (n := r)) (Quotient.out y) = y from Quotient.out_eq y] at h
    exact h.symm
  rw [he]
  set_option synthInstance.maxHeartbeats 200000 in
  refine Integrable.of_bound (CuspidalSpectrum.continuous_cuspQuot hHl hHc).aestronglyMeasurable
    (|C| * (2 * AutomorphicForm.heightConst E (r + s) * L) ^ N * D) (Filter.Eventually.of_forall fun q => ?_)
  obtain ⟨y, rfl⟩ := mk_surjective (rationalGLOne (K := E) (n := r)) q
  rw [CuspidalSpectrum.cuspQuot_mk]
  exact hbound y
end

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.constantTerm_heckeOperator_eq_sum_satake :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (w : Pl E) (ϖ : w.adicCompletion E) (hϖ : ϖ ∈ Ov E w) (hu : IsUnifV E w ϖ)
      [Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩)] (j : ℕ), j ≤ r + s → ∀ φ : Sm E (r + s), Umg φ → (∀ k ∈ KGL w (n := (r + s)), rw (r + s) w k φ = φ) → ∀ (x : GA E r) (m : GA E s),
      AutomorphicForm.constantTerm r (heckeVec (rw (r + s) w) (KGL w (n := (r + s))) (Tj ℂ (r + s) (Ov E w) ϖ j) φ).1 (lev (Ad E) r s (x, m)) =
        ∑ p : Fin (r + 1) × Fin (s + 1), UpperTheory.V.Cj.S.coef (qV E w) r s j p *
          ∑ i₁ : SatakeIdx w hϖ (n := r) p.1, ∑ i₂ : SatakeIdx w hϖ (n := s) p.2,
            AutomorphicForm.constantTerm r φ.1 (lev (Ad E) r s (x * finGL E r (locGL E r w (satakeB w hϖ hu i₁)), m * finGL E s (locGL E s w (satakeB w hϖ hu i₂)))) := by
  intro E _ _ _ r s w ϖ hϖ hu _ j hj φ hφ hK x m
  have hc : Continuous φ.1 := ((UpperTheory.ConvolutionTheory.BW.umgOps E (r + s)).2 φ hφ).1
  obtain ⟨b1, b2, b3, -⟩ := UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding E w r s
  have h1 := UpperTheory.V.Cj.S.hkSum E w (r + s) (Sm E (r + s)) (rw (r + s) w) ϖ hϖ hu j hj φ (GlobalTheory.LGrp.mem_fixed.2 hK)
  have h2 : ∀ g, AutomorphicForm.constantTerm r (heckeVec (rw (r + s) w) (KGL w (n := (r + s))) (Tj ℂ (r + s) (Ov E w) ϖ j) φ).1 g =
      ∑ i : SatakeIdx w hϖ (n := r + s) j,
        AutomorphicForm.constantTerm r φ.1 (g * finGL E _ (locGL E _ w (satakeB w hϖ hu i))) := fun g => by
    unfold AutomorphicForm.constantTerm
    rw [← integral_finsetSum _ fun i _ => AutomorphicForm.integrableOn_constantTerm hc _, h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, ← mul_assoc]
    rfl
  rw [h2, ← UpperTheory.blockDiagonal_eq_leviEmbedding, UpperTheory.V.Cj.S.hkLocal UpperTheory.V.Cj.S.sumInner UpperTheory.V.Cj.S.matBlock E w r s ϖ hϖ hu j
    (fun g => AutomorphicForm.constantTerm r φ.1 (UpperTheory.V.Af.Fin.blk x m * finGL E _ (locGL E _ w g))) (fun X g => by
      obtain ⟨Y, hY⟩ := b2 X
      obtain ⟨Y', hY'⟩ := b3 x m Y
      simp only [map_mul]
      rw [hY, ← mul_assoc, hY', mul_assoc, PositivityTheory.Rg.Rs.SliceClasses.constantTerm_unipGL_mul hφ.left])]
  simp only [b1]
  simp only [UpperTheory.blockDiagonal_eq_leviEmbedding, ← map_mul, Prod.mk_mul_mk]
end

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private def zGL {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) : GL (Fin r) L :=
  Units.map ((Matrix.scalar (Fin r) : L →+* Matrix (Fin r) (Fin r) L) : L →* Matrix (Fin r) (Fin r) L) (Units.mk0 π hπ)

private theorem zGL_val {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) :
    ((zGL r hπ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) = Matrix.diagonal fun _ => π := rfl

private theorem zGL_comm {L : Type} [Field L] (r : ℕ) {π : L} (hπ : π ≠ 0) (g : GL (Fin r) L) :
    zGL r hπ * g = g * zGL r hπ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, zGL_val]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

private theorem card_top {r a : ℕ} (h : a ≤ r) :
    ((Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ).card = a := by
  rw [Finset.card_compl, Fintype.card_fin, Fin.card_filter_val_lt]
  omega

private theorem inv_mem {E : Type} [Field E] [NumberField E] (w : Pl E) {r a : ℕ} (har : a ≤ r)
    {ϖ : w.adicCompletion E} (hπ : ϖ ≠ 0) {b : GL (Fin r) (w.adicCompletion E)}
    (hb : b ∈ satakeTset w ϖ (r - a)) : b⁻¹ * zGL r hπ ∈ satakeTset w ϖ a := by
  classical
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hb
  set S : Finset (Fin r) := (Finset.univ.filter fun i : Fin r => (i : ℕ) < r - a)ᶜ with hSdef
  have hS : S.card = a := card_top har
  set G := satakeGL (Ov E w) hπ S (fun _ => 0) with hGdef
  have hG : G ∈ satakeTset w ϖ a := by
    obtain ⟨x, hx, y, hy, e'⟩ := satakeGL_mem_doset (Ov E w) hπ S (fun _ => 0)
    rw [hS] at e'
    exact ⟨x, hx, y, hy, e'⟩
  have hGv : (G : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = satakeD ϖ S := by
    have h0 : satakeN (Ov E w) S (fun _ => 0) = 0 := by
      ext i j
      simp [satakeN]
    show (1 + satakeN (Ov E w) S (fun _ => 0)) * satakeD ϖ S = _
    rw [h0, add_zero, Matrix.one_mul]
  set d : GL (Fin r) (w.adicCompletion E) := k₁⁻¹ * b * k₂⁻¹ with hddef
  have hd : (d : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = diagJ r ϖ (r - a) := by
    rw [hddef, Units.val_mul, Units.val_mul, e]
    have h1 : ((k₁⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        (k₁ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (k₂ : Matrix (Fin r) (Fin r) (w.adicCompletion E)) *
        ((k₂⁻¹ : GL (Fin r) (w.adicCompletion E)) : Matrix (Fin r) (Fin r) (w.adicCompletion E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hGd : G * d = zGL r hπ := by
    apply Units.ext
    rw [Units.val_mul, hGv, hd, zGL_val]
    unfold satakeD diagJ
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : (i : ℕ) < r - a
    · simp [hSdef, h]
      intro h'
      omega
    · simp [hSdef, h]
      intro h'
      omega
  have hb' : b = k₁ * d * k₂ := by
    rw [hddef]; group
  have hz : d⁻¹ * zGL r hπ = G := by
    rw [← zGL_comm, ← hGd]; group
  have hfin : b⁻¹ * zGL r hπ = k₂⁻¹ * G * k₁⁻¹ := by
    rw [← hz, hb', mul_inv_rev, mul_inv_rev]
    have := zGL_comm r hπ k₁⁻¹
    simp only [mul_assoc]
    rw [← this]
  rw [hfin]
  exact satake_Tset_right w (satake_Tset_left w hG ((GLint _ _).inv_mem hk₂)) ((GLint _ _).inv_mem hk₁)

theorem UpperTheory.exists_satakeTset_sum_eigenvector :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r →
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (f : V) (B : Multiset ℂˣ), IsSatVecGL w ρ f B →
      ∃ (n : ℕ) (c : Fin n → GL (Fin r) (w.adicCompletion E)) (μ : ℂ), 0 < n ∧ (∀ i, (c i)⁻¹ ∈ satakeTset w ϖ a) ∧ ∑ i, ρ (c i) f = μ • f := by
  intro E _ _ w r a ϖ hu har V _ _ ρ f B hf
  classical
  obtain ⟨hf0, hfix, -, hT⟩ := hf
  have hϖ := mem_Ov_of_isUnifV hu
  have hπ : ϖ ≠ 0 := satake_unif_ne_zero w hu
  letI : Fintype (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) := @Fintype.ofFinite _ (satake_res_finite w hϖ hu)
  have hne : ∀ j, j ≤ r → Nonempty (SatakeIdx w hϖ (n := r) j) := by
    intro j hj
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin r))) (n := j)
      (by simpa using hj)
    exact ⟨⟨⟨S, hS⟩, fun _ => 0⟩⟩
  have hsum : ∀ j, j ≤ r → ∑ i : SatakeIdx w hϖ (n := r) j, ρ (satakeB w hϖ hu i) f =
      satEig (qV E w) r B j • f := fun j hj => by
    rw [← UpperTheory.V.Cj.S.hkSum E w r V ρ ϖ hϖ hu j hj f hfix, hT ϖ hu j hj]
  set z := zGL r hπ with hzdef
  have hfx : ∀ k ∈ KGL w (n := r), ρ k f = f := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hfix _ hk
  have hB : ∀ i : SatakeIdx w hϖ (n := r) r, ρ (satakeB w hϖ hu i) f = ρ z f := by
    intro i
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := satakeB_mem w hϖ hu i
    have hdz : diagJ r ϖ r = (z : Matrix (Fin r) (Fin r) (w.adicCompletion E)) := by
      rw [hzdef, zGL_val]
      unfold diagJ
      congr 1
      funext i
      simp [i.isLt]
    have : satakeB w hϖ hu i = z * (k₁ * k₂) := by
      apply Units.ext
      rw [e, hdz, ← Units.val_mul, ← Units.val_mul, hzdef, ← zGL_comm, mul_assoc]
    rw [this, map_mul, Module.End.mul_apply, hfx _ ((KGL w (n := r)).mul_mem hk₁ hk₂)]
  obtain ⟨i₀⟩ := hne r le_rfl
  have hcard : (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ) ≠ 0 := by
    have : Fintype.card (SatakeIdx w hϖ (n := r) r) ≠ 0 := by
      haveI : Nonempty (SatakeIdx w hϖ (n := r) r) := ⟨i₀⟩
      exact Fintype.card_ne_zero
    exact_mod_cast this
  set c : ℂ := (Fintype.card (SatakeIdx w hϖ (n := r) r) : ℂ)⁻¹ * satEig (qV E w) r B r with hcdef
  have hzf : ρ z f = c • f := by
    have h := hsum r le_rfl
    simp only [hB, Finset.sum_const, Finset.card_univ] at h
    rw [hcdef, mul_smul, ← h, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hzf
    apply hf0
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hzf, map_zero]
  have hzi : ρ z⁻¹ f = c⁻¹ • f := by
    have : ρ z⁻¹ (ρ z f) = f := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hzf, map_smul] at this
    rw [eq_inv_smul_iff₀ hc]
    exact this
  obtain ⟨i₁⟩ := hne (r - a) (Nat.sub_le _ _)
  let e := Fintype.equivFin (SatakeIdx w hϖ (n := r) (r - a))
  refine ⟨Fintype.card (SatakeIdx w hϖ (n := r) (r - a)), fun i => z⁻¹ * satakeB w hϖ hu (e.symm i),
    satEig (qV E w) r B (r - a) * c⁻¹, Fintype.card_pos_iff.2 ⟨i₁⟩, fun i => ?_, ?_⟩
  · rw [mul_inv_rev, inv_inv]
    exact inv_mem w har hπ (satakeB_mem w hϖ hu _)
  · rw [Equiv.sum_comp e.symm (fun i => ρ (z⁻¹ * satakeB w hϖ hu i) f)]
    simp only [map_mul, Module.End.mul_apply]

    rw [← map_sum, hsum _ (Nat.sub_le _ _), map_smul, hzi, smul_smul]
end
