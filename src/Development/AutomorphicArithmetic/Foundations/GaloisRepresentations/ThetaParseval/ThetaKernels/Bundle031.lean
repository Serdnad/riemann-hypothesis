module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle021
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle014
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle446
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.HgtMulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ExistsNeZeroOfMap
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.TBlkEqTFMulProdTV
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fcAll_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) →
      fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T x = a * fc d.B.ψ d.b nb lam 𝓖 f T x + fc d.B.ψ d.b nb lam 𝓖 f' T x) ∧
    ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ C, ‖f y‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T x‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
  have hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M := by
    intro f M hf hM β
    obtain ⟨k, hk, e⟩ := hper f hf β
    rw [norm_mul, hχn β, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    intro f hfc hf
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hfc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun β => hbd f M hf hM β
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩
  · simp only [fc]
    have e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1
theorem fcCont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (f : d.G → ℂ)
    (hf : Continuous f) (hi : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) : Continuous fun x => fc d.B.ψ d.b nb lam 𝓖 f T x := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  obtain ⟨iTG, iLCG, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have hmul : Continuous fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2 := (hcont.comp continuous_fst).mul continuous_snd
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  have hKN : IsCompact ((fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2) '' (K ×ˢ N)) := (hK.prod hN).image hmul
  obtain ⟨M, hM⟩ := hKN.exists_bound_of_continuousOn hf.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hf.comp (hcont.mul continuous_const)).mul hχc).aestronglyMeasurable
  · filter_upwards [hNx] with x hx
    refine Filter.Eventually.of_forall fun β => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hχn β, mul_one]
    have : f (nb β * x) = f (nb (γ + β) * x) := by
      rw [kfour.nb_add hnb, mul_assoc, hi _ (kfour.nb_rat hnb γ hγ)]
    rw [this]
    exact hM _ ⟨(γ + β, x), ⟨hk, hx⟩, rfl⟩
  · exact Filter.Eventually.of_forall fun β =>
      ((hf.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem majorant_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hS : d.Strong) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ C : Set d.G, IsCompact C →
      ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q := by
  obtain ⟨r', s', hY⟩ := hS
  have hKc : IsCompact (d.K : Set d.G) := _root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨hac, hpos⟩ := _root_.GlobalTheory.T.height_function_continuous_pos F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.flat_section_growth_bound d.K d.a hKc d.ok.hgt hpos d.χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.GlobalTheory.T.eisenstein_series_convergence_bound F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  refine ⟨σ₀ - (d.n : ℝ) / 2, fun z hz C hC => ?_⟩
  set σ' : ℝ := z.re + (d.n : ℝ) / 2 with hσ'
  have h1 : σ₀ < σ' := by linarith
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup d.G := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hKC : IsCompact ((d.K : Set d.G) * C) := hKc.mul hC
  obtain ⟨M, hM⟩ := hKC.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M', hM'⟩ := hKC.exists_bound_of_continuousOn (hac.inv₀ fun y => (hpos y).ne').continuousOn
  have hr : ∀ x, ∀ c ∈ C, d.a (x * c) ^ σ' ≤ (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a x ^ σ' := by
    intro x c hc
    obtain ⟨k, hk, e⟩ := hgt_mul_right d.ok.hgt x c
    have hkc : k * c ∈ (d.K : Set d.G) * C := Set.mul_mem_mul hk hc
    have r0 := hpos (k * c)
    have rM : d.a (k * c) ≤ |M| := (Real.le_norm_self _).trans ((hM _ hkc).trans (le_abs_self M))
    have hm := hM' _ hkc
    rw [Pi.inv_apply, norm_inv, Real.norm_of_nonneg r0.le] at hm
    have hM'pos : 0 < |M'| := lt_of_lt_of_le (inv_pos.2 r0) (hm.trans (le_abs_self _))
    have rm : |M'|⁻¹ ≤ d.a (k * c) := (inv_le_comm₀ hM'pos r0).2 (hm.trans (le_abs_self _))
    have hb : d.a (k * c) ^ σ' ≤ |M| ^ σ' + (|M'|⁻¹) ^ σ' := by
      rcases le_total 0 σ' with hs | hs
      · exact (Real.rpow_le_rpow r0.le rM hs).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _))
      · exact (Real.rpow_le_rpow_of_nonpos (inv_pos.2 hM'pos) rm hs).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    rw [e, Real.mul_rpow (hpos x).le r0.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hpos x).le _)
  obtain ⟨_, _, hsum⟩ := hσ σ' h1
  refine ⟨fun q => |C0| * (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a ((Quotient.out q).1 * 1) ^ σ', (hsum 1).1.mul_left _,
    fun g hg q => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = _root_.GlobalTheory.ThK.Dbl.flat d.a f s₁ z := funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, _root_.GlobalTheory.ThK.Dbl.flat]
    rw [Real.coe_toNNReal _ (hpos y).le]
  rw [hΦ]
  show ‖_root_.GlobalTheory.ThK.Dbl.flat d.a f s₁ z ((Quotient.out q).1 * g)‖ ≤ _
  simp only [mul_one]
  calc _ ≤ C0 * d.a ((Quotient.out q).1 * g) ^ σ' := hC0 z _
    _ ≤ |C0| * d.a ((Quotient.out q).1 * g) ^ σ' := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (hpos _).le _)
    _ ≤ |C0| * ((|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a (Quotient.out q).1 ^ σ') :=
        mul_le_mul_of_nonneg_left (hr _ g hg) (abs_nonneg _)
    _ = _ := by ring
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eta_sign_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) {ε : ℤˣ}
    (hb : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    σ η = -(((ε : ℤ) : E)) * η := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have he := frame_sign hσ d.ok.hn d.Y.J (-1) (fun i j => by rw [hY, neg_one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 1
      (by rw [one_smul]; exact ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.herm] at h
    rw [he, neg_neg, one_mul]
    exact mul_right_cancel₀ hij h
  · have he := frame_sign hσ d.ok.hn d.Y.J 1 (fun i j => by rw [hY, one_mul]) d.b ε hb
    obtain ⟨i, j, hij⟩ := exists_ne_zero_of_map d.A.J (d.B.emb w).1 Complex.I (ne_zero_of_sig d.ok.hm _ (hA.sig w))
    have h := herm i j
    rw [map_mul, hA.skew] at h
    rw [he, neg_one_mul]
    apply mul_right_cancel₀ hij
    linear_combination -h
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem perLift_k (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n < d.m) (hEA : d.EisAll) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn}
    (hφ : R.IsLift w Ψ φ) (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (d.I (φ P) x) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _)]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1
      map_smul' := fun a P => by rw [map_smul]; exact _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1 }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, ⟨ε, ww, hww, -⟩, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hsec1 : IsSec d.K d.χ (s0 d.m d.n) (d.sec0 (φ 1)) := hSK F E σ d (φ 1) (hKF 1)
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht
      sl Il d.lamSet :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1
      Ileft := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2
      Ik := by
        intro P g k hk
        show thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := fun g a b P => hGI F E σ d R w Ψ hΨ φ hφ g a b P
      Idil := hGD F E σ d R w Ψ hΨ φ hφ
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩
      Λadd := fun l hl => (hLB F E σ d l hl).1
      Λbd := fun l hl => (hLB F E σ d l hl).2
      Λsing := fun f hf hinv hz => hLS F E σ d R w f hf hinv hz
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x, hcd, hT, rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ hsec1 hE1
        have hWh := hW F E σ d hnm hEA (φ 1) (hKF 1) nb lam 𝓖 hcd ε ww hww T hT x
        have hC := hTC F E σ d (φ 1) (hφ 1).1 nb lam 𝓖 hcd T x
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z) T x) (s0 d.m d.n)
          (fc d.B.ψ d.b nb lam 𝓖 (d.I (φ 1)) T x)
        rw [hC]
        exact hWh.congr ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x).2 T hT).symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm.le)
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il d.lamSet hGDat P x
theorem mainOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainOf_k := by
  intro hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW F E _ _ _ _ _ σ d hnm hEA Φ hΦ x
  obtain ⟨R⟩ := hRD F E σ d
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hsch : ∀ i, φ i (P i) ∈ d.sch := fun i => (hφ i (P i)).1
  have eT : ∀ i, d.T (φ i (P i)) = R.tens w (fP (P i)) (Ψ i) := fun i => (hφ i (P i)).2
  have hΦeq : Φ = ∑ i, φ i (P i) := by
    have hmem : Φ - ∑ i, φ i (P i) ∈ d.sch := d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => hsch i)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)

    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, eT, hsum, sub_self]
  have key : ∀ i, HolValueAt (fun z => d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x) (s0 d.m d.n)
      (d.I (φ i (P i)) x) := fun i =>
    _root_.PositivityTheory.SiegelWeilFormula.KMain.perLift_k hA hT hTC hAux hFM hLo hLI hGS hGI hGD hPK hSK hLB hLS hU hW d hnm hEA R w (hΨ i) (hφ i) (P i) x
  have hv : d.I Φ x = ∑ i, d.I (φ i (P i)) x := by
    rw [hΦeq, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hsch i) (by rw [eT]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hKi i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 Φ = fun y => ∑ i, d.sec0 (φ i (P i)) y := by
    funext y

    rw [hΦeq, ← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    rfl
  have heq : EqRight (fun z => ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x (fun i _ => htt i z (hz' i))
    show ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x = d.eis (d.sec0 Φ) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    simp only [Finset.mul_sum]
    exact this.symm
  rw [hv]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
end PositivityTheory.SiegelWeilFormula.KMain
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isClosed_siegel_parabolic (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsClosed (par2 σ d.Y : Set d.G) := by
  have e : (par2 σ d.Y : Set d.G) = (fun p : d.G => (inFrame d.b p).toBlocks₂₁) ⁻¹' {0} := by
    ext p
    exact mem_stabiliser_iff_frame_lower_block d.ok.frame p
  rw [e]
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  exact isClosed_singleton.preimage
    (continuous_pi fun i => continuous_pi fun j => hfr.matrix_elem (Sum.inr i) (Sum.inl j))
theorem continuous_a'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Continuous d.a := by
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.isClosed_siegel_parabolic d) (_root_.PositivityTheory.SiegelWeilFormula.kunf.isCompact_K_k d)
    (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g
    exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · have hc : Continuous fun x : par2 σ d.Y × d.K => ((GlobalTheory.Doubling.absE F E (kunf.SecA.uDet x.1) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (kunf.SecA.continuous_uDet.comp continuous_fst))
    refine hc.congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    rw [d.ok.hgt.val _ t ht _ x.2.2, kunf.SecA.uDet_eq ht]
end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.ae_ext (z z' : AE F E) (h : ∀ w, piInf (d.B.emb w) z = piInf (d.B.emb w) z') (hf : finOne F • z = finOne F • z') :
    z = z' :=
  Place.ad_ext d.cm d.B.emb h hf
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.exists_insW (w : InfinitePlace F) : ∃ ins : ℂ →+ AE F E, (∀ z, piInf (d.B.emb w) (ins z) = z) ∧
    (∀ w', w' ≠ w → ∀ z, piInf (d.B.emb w') (ins z) = 0) ∧ ∀ z, finOne F • ins z = 0 := by
  obtain ⟨s, -, h1, h2, h3, -⟩ := Place.exists_sec d.cm d.B.emb
  refine ⟨AddMonoidHom.mk' (fun z => s (Pi.single w z)) (fun a b => by rw [Pi.single_add, h3]), fun z => ?_,
    fun w' hw' z => ?_, fun z => h2 _⟩
  · simp [h1]
  · simp [h1, Pi.single_eq_of_ne hw']
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem fourierZero_k : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k := by
  intro F E _ _ _ _ _ σ d nb lam 𝓖 hc f hf hper hfc
  funext g
  exact _root_.PositivityTheory.FTA.ZFC.fc_inj_pt_per_k d.ok.good d.b nb lam 𝓖 d.ok.frame hc f hf hper g fun T => hfc T g
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end
