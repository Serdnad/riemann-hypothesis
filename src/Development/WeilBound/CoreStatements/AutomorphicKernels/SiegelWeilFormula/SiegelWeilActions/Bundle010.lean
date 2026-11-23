module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousPhz
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.Bundle001
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.ExistsGlCol
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle003

@[expose] public section

section

set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

open ComplexParameterFamilyContinuity

theorem cptDom : CptDom := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := kfour.sigma_sigma_of_good d.ok.good
    obtain ⟨hlc, hsc, ht2, hbo⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨hnb, hlam, hfd, h1⟩ := h
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' (nF σ d.Y d.b) hK hc lam
    exact ⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
  · obtain ⟨hfr, hν, hfd, h1⟩ := h
    haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K :=
      ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩

theorem absConv : AbsConv := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := continuous_uM L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (phz d f s₁ z) := continuous_phz d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  have hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖) := hc𝓤.prod hc𝓖
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · have eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅ := (show Disjoint (closure 𝓤)ᶜ 𝓤 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq
      have eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅ := (show Disjoint (closure 𝓖)ᶜ 𝓖 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq
      refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]
  have hbd : ∀ q : Cs d, ∀ᵐ p ∂μ, ‖kq L f s₁ z nb T uM (rep q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [kq, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : Cs d, Continuous (kq L f s₁ z nb T uM (rep q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]

end PositivityTheory.SiegelWeilFormula.Act

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem stab_dec (h : Hyp L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : Fix L x) :
    ∃ (s : d.G) (c : Cr L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (emS L) (emS L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (emS L) (emS L) with hH_def
  have hH := blockH_form L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * padE L H') := by
    rw [hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, inFrame_j, hg'i, padM_incM, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * padE L H') := nq_E L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (j_rat L (inv_mem hg'r))
  set N0 := G0 * padE L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := delta_par h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : Cr L := ⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (cM_rat' h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = sExp L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := U_sExp (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            ((sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            (sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (nq_sExp _ _) (nq_cM h _)
    · obtain ⟨r1, r2, r3, r4⟩ := row_sC h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          have hc : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun _ => rfl

          simp [incM, GlobalTheory.ThK.incV, hc, map_add (f := _), map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = sExp L e (GlobalTheory.ThK.incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    rw [hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, w1_conj_sExp_mem_par2 h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end
