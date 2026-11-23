module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CoverFourierCoeffEqFiniteFourierSum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle095
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_of_abs_sub_le_eventually (a q : ℕ → ℝ) (I G W V C : ℝ) (hC : 0 ≤ C) (hq : Tendsto q atTop (𝓝 G))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, |a m - I - ε * W| ≤ C * (G + ε * V - q m)) : Tendsto a atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hK : 0 < |W| + C * |V| + 1 := by positivity
  set ε := e / (2 * (|W| + C * |V| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hq' := Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)
  filter_upwards [h ε hε0, hq'] with m hm hqm
  rw [Real.dist_eq] at hqm ⊢
  have h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W| := by
    have := abs_add_le (a m - I - ε * W) (ε * W)
    rw [abs_mul, abs_of_pos hε0] at this
    simpa using this
  have h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := neg_abs_le (q m - G)
    have := le_abs_self V
    nlinarith
  have h3 : C * |q m - G| ≤ (C + 1) * |q m - G| := by nlinarith [abs_nonneg (q m - G)]
  have h4 : (C + 1) * |q m - G| < e / 2 := by
    have := mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)
    rwa [mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)] at this
  have h5 : ε * (|W| + C * |V|) < e / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg W, abs_nonneg V]
  nlinarith

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem tendsto_finsum_integral_berg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  intro k _ X _ p D hX hG P hpos ω r f hf hli hr w hw
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hcpt : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hfm : ∀ σ, IsFiniteMeasure (ω σ).meas := fun σ => (GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)).1
  choose ρ hρR hρ0 hρint using fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hG P.L hpos σ (ω σ)
  have hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C := fun σ g hg => by
    haveI := hcpt σ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  have hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas := fun σ g hg => by
    haveI := hfm σ
    obtain ⟨C, hC⟩ := hbd σ g hg
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)
  set C : ℝ := ∑ σ, |Cw σ| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwC : ∀ σ y, |w σ y| ≤ C := fun σ y => (hCw σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw
  set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'
  set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW
  set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV
  have hch : chInt P.L D w = Iw := by
    simp only [chInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)
  have hgd : gdeg P.L D = G' := by
    simp only [gdeg, chInt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hρint σ _ continuous_const]
    simp
  rw [hch]
  rw [hgd] at hr
  refine tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial)
    (G' / D.factorial) W V C hC0 hr fun ε hε => ?_
  filter_upwards [GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1
  obtain ⟨hfam, hpd, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  obtain ⟨hBi, hBs, hB0, hBx⟩ := GlobalTheory.T.bergman_function_total_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m))
    (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd
  set M : ℝ := (m : ℝ) ^ D with hMdef
  have hM : 0 < M := pow_pos (by exact_mod_cast hm1) D
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M :=
    fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le)
      fun c => hmo (Fin (r m)) (f m) (hf m) c σ y
  have hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas := fun σ => by
    haveI := hfm σ
    exact (((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M
  have hl1 := abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas)
    (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle
    (fun σ => (hw σ).measurable) hC0 hwC
  have e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas =
      M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas := fun σ => by
    have h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas := hint σ _ ((hw σ).mul (hρR σ).1)
    have h2 := hint σ _ (hw σ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext y; ring
  have e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas =
      M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas := fun σ => by
    haveI := hfm σ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]
    congr 1; funext y; ring
  simp only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢
  simp only [Fintype.card_fin] at hBs
  rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs] at hl1
  rw [← hIw, ← hW, ← hG', ← hV] at hl1
  set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA
  have eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M := by
    field_simp
    ring
  rw [eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M =
      C * (M / D.factorial * G' + M * ε * V - (r m : ℝ)) := by
    field_simp
  rw [eq2]
  exact hl1

end GlobalTheory.HSAmp
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFramesD.symp_framesD | exact GlobalTheory.SympFramesD.symp_framesD | (intros; apply GlobalTheory.SympFramesD.symp_framesD <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.CoverTransform

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

theorem qRep_sub_mem {K : Submodule (𝓞 E) Dw.La} (a : Dw.La) :
    qRep (Submodule.Quotient.mk a : Dw.La ⧸ K) - a ∈ K :=
  (Submodule.Quotient.eq _).1 (GlobalTheory.HalfPairing.qRep_mk _)

theorem pd_mem_half (d : DeltaDat Xo c n) (h : d.IsLev) :
    (d.pd : 𝓞 E) ∈ d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have h1 : (d.pd : 𝓞 E) ∈ d.I * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [GlobalTheory.LevelCoverDatum.half_mul_conj d h]; exact Ideal.mem_span_singleton_self _
  exact Ideal.mul_le_right h1

theorem mfr_cover (d : DeltaDat Xo c n) (h : d.IsLev) :
    Mfr d.l₂ = Mfr l * d.I.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold Mfr; rw [h.2.2.2.1, Ideal.map_mul]

theorem finite_laJ (d : DeltaDat Xo c n) (h : d.IsLev) : Finite (LaJ Xo c d) := by
  have hp := GlobalTheory.LevelCoverDatum.pd_pos d h
  have hb : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro e
    have := pd_mem_half d h
    rw [e, Ideal.mem_bot] at this
    exact hp.ne' (by exact_mod_cast this)
  have := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)).finiteQuotientOfFreeOfNeBot hb
  have := Dw.fin
  exact Submodule.finite_quotient_smul _ (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem exists_bezout (d : DeltaDat Xo c n) (h : d.IsLev) :
    ∃ α β : 𝓞 E, α * d.pd + β * l.M = 1 := Nat.Coprime.cast (R := 𝓞 E) h.2.2.1

theorem mem_half_of_smul (d : DeltaDat Xo c n) (h : d.IsLev) {u : Dw.La}
    (hu : l.M • u ∈ (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) :
    u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  have h1 : l.M • u ∈ (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La) :=
    Submodule.smul_mono_left (by rw [mfr_cover d h]; exact Ideal.mul_le_right) hu
  have h2 : u = (α * d.pd) • u + β • l.M • u := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, ← add_smul, e, one_smul]
  rw [h2]
  exact add_mem (Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) trivial) (Submodule.smul_mem _ _ h1)

theorem exists_class (d : DeltaDat Xo c n) (h : d.IsLev) {x u : Dw.La}
    (hu : u - d.pd • x ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) :
    ∃ z : LaJ Xo c d, (Submodule.Quotient.mk (d.pd • x + l.M • qRep z) : LevQc Dw d.l₂) = Submodule.Quotient.mk u := by
  obtain ⟨α, β, e⟩ := exists_bezout d h
  refine ⟨Submodule.Quotient.mk (β • (u - d.pd • x)), (Submodule.Quotient.eq _).2 ?_⟩
  have h1 := qRep_sub_mem (K := (d.I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) Dw.La)) (β • (u - d.pd • x))
  generalize qRep (Submodule.Quotient.mk (β • (u - d.pd • x)) : LaJ Xo c d) = r at h1 ⊢
  have h2 : d.pd • x + l.M • r - u =
      (l.M : 𝓞 E) • (r - β • (u - d.pd • x)) - (α * d.pd) • (u - d.pd • x) := by
    have e' : α * (d.pd : 𝓞 E) = 1 - l.M * β := by linear_combination e
    rw [e', ← Nat.cast_smul_eq_nsmul (𝓞 E) l.M]
    generalize d.pd • x = v
    module
  rw [h2, mfr_cover d h]
  refine sub_mem ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul (GlobalTheory.Dict.CoverFourier.natCast_mem l).2 h1
  · rw [mul_comm (Mfr l), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ _ (pd_mem_half d h)) hu

theorem dvd_pairing (d : DeltaDat Xo c n) (h : d.IsLev) (x z y : Dw.La) :
    (d.l₂.M : ℤ) ∣ Dw.EF (qRep (Submodule.Quotient.mk (d.pd • x + l.M • z) : LevQc Dw d.l₂)) (cSep d.l₂ • y) -
      (d.pd * Dw.EF x (cSep l • y) + l.M * Dw.EF z (cHalf H d.I • y)) := by
  have h1 := GlobalTheory.LevelPairing.dvd_left (l := d.l₂) y
    (qRep_sub_mem (K := (Mfr d.l₂ • ⊤ : Submodule (𝓞 E) Dw.La)) (d.pd • x + l.M • z))
  obtain ⟨a1, a2⟩ := GlobalTheory.LevelPairing.cSep_spec d.l₂
  obtain ⟨b1, b2⟩ := GlobalTheory.LevelPairing.cSep_spec l
  have h2 : (l.M : ℤ) ∣ Dw.EF x ((cSep d.l₂ - cSep l) • y) := by
    refine GlobalTheory.HalfPairing.dvd_of_mem _ _ _ ?_
    rw [← l.prod, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 l.coprime)]
    refine ⟨?_, sub_mem ?_ b1⟩
    · simpa using sub_mem (h.1.2.1 a2) b2
    · rw [mfr_cover d h] at a1
      exact Ideal.mul_le_left a1
  have h3 := GlobalTheory.Dict.CoverFourier.pd_dvd d h (by rw [mfr_cover d h]; exact Ideal.mul_le_right) z
    (a := y) (a' := y) (by rw [sub_self]; exact zero_mem _)
  have hM : (d.l₂.M : ℤ) = l.M * d.pd := by rw [h.2.1]; push_cast; rfl
  have h4 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_right h2 (d.pd : ℤ)
  have h5 : (d.l₂.M : ℤ) ∣ _ := hM ▸ mul_dvd_mul_left (l.M : ℤ) h3
  have h6 := dvd_add (dvd_add h1 h4) h5
  simp only [map_sub, map_add (f := _), map_nsmul, sub_smul, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    nsmul_eq_mul] at h6
  refine h6.trans (dvd_of_eq ?_)
  ring

end

theorem hatC_eq_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (xJ : Fin n → LaJ Xo c d), d.PhiPin ph ψ xJ → ∀ (x₀ : Fin n → Dw.La) (ζ : ℂ) (φc : (Fin n → LevQc Dw d.l₂) → ℂ), (∀ z : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (d.pd • x₀ b + l.M • z b)) = ζ * ((ph (fun b => Submodule.Quotient.mk (z b)) : c.F) : ℂ)) → (∀ x : Fin n → Dw.La, φc (fun b => Submodule.Quotient.mk (x b)) ≠ 0 → ∀ b, x b - d.pd • x₀ b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)) → GlobalTheory.AdTh.hatC d.l₂ φc = fun q => ζ * ((d.eF.symm (d.w x₀ q) : c.F) : ℂ) := by
  intro E _ _ _ H Dw l Xo c n d hd ph ψ xJ hpin x₀ ζ φc hval hsupp
  funext q
  haveI := finite_laJ d hd
  haveI := GlobalTheory.AdTh.PairModel.finite_levQc Dw d.l₂
  haveI := Fintype.ofFinite (Fin n → LaJ Xo c d)
  haveI := Fintype.ofFinite (Fin n → LevQc Dw d.l₂)
  have hM₂ : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have he : zeta d.l₂.M ^ d.l₂.M = 1 := (Complex.isPrimitiveRoot_exp _ hM₂).pow_eq_one
  have he0 : zeta d.l₂.M ≠ 0 := Complex.exp_ne_zero _
  have hz : d.c₂.F.val (zetaM d.c₂) = zeta d.l₂.M := GlobalTheory.LevelPairing.zetaM_coe d.c₂
  have hz1 : c.F.val (zetaM c) = zeta d.l₂.M ^ d.pd := by
    rw [← hz, ← map_pow, GlobalTheory.LevelCoverDatum.zetaM_cover d hd.2.1]; rfl
  have hφ : c.F.val (d.φδ q) = ∑ z : Fin n → LaJ Xo c d, ((ph z : c.F) : ℂ) * (zeta d.l₂.M ^ l.M) ^
      (∑ b, Dw.EF (qRep (z b)) (cHalf H d.I • levRep (q b))) := by
    change d.c₂.F.val (d.eF (d.φδ q)) = _

    rw [hpin.2.2.2.2.2 q, finsum_eq_sum_of_fintype, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, map_zpow₀, ← GlobalTheory.Dict.CoverFourier.zetaM_pow d hd, map_pow, hz]
    rfl
  rw [DeltaDat.w, AlgEquiv.symm_apply_apply]
  change _ = ζ * c.F.val (zetaM c ^ pairL (l := l) x₀ (fun b => levRep (q b)) * d.φδ q)
  rw [map_mul, map_zpow₀, hz1, hφ, Finset.mul_sum, Finset.mul_sum, GlobalTheory.AdTh.hatC, finsum_eq_sum_of_fintype]
  symm
  refine Fintype.sum_of_injective
    (fun (z : Fin n → LaJ Xo c d) b => (Submodule.Quotient.mk (d.pd • x₀ b + l.M • qRep (z b)) : LevQc Dw d.l₂))
    (fun z z' e => funext fun b => ?_) _ _ (fun x hx => ?_) (fun z => ?_)
  · have h1 := (Submodule.Quotient.eq _).1 (congrFun e b)
    rw [add_sub_add_left_eq_sub, ← smul_sub] at h1
    rw [← GlobalTheory.HalfPairing.qRep_mk (z b), ← GlobalTheory.HalfPairing.qRep_mk (z' b)]
    exact (Submodule.Quotient.eq _).2 (mem_half_of_smul d hd h1)
  · refine mul_eq_zero_of_left ?_ _
    by_contra hne
    have hx' : (fun b => (Submodule.Quotient.mk (qRep (x b)) : LevQc Dw d.l₂)) = x :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    choose z hz' using fun b => exists_class d hd (hsupp (fun b => qRep (x b)) (by rwa [hx']) b)
    exact hx ⟨z, (funext hz').trans hx'⟩
  · have hz' : (fun b => (Submodule.Quotient.mk (qRep (z b)) : LaJ Xo c d)) = z :=
      funext fun b => GlobalTheory.HalfPairing.qRep_mk _
    rw [hval (fun b => qRep (z b)), hz', mul_left_comm, ← mul_assoc ζ, mul_left_comm]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ he0]
    symm
    refine GlobalTheory.Dict.CoverFourier.zpow_congr' hM₂ he ?_
    rw [pairL, pairL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun b _ => dvd_pairing d hd _ _ _

end GlobalTheory.CoverTransform
end

section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

variable {p : ℕ} [Fact p.Prime]

theorem exists_int_of_den_le (D k : ℕ) (hD : 0 < D) (q : ℚ)
    (h1 : ∀ ℓ : ℕ, ℓ ≠ p → q.den.factorization ℓ ≤ D.factorization ℓ) (h2 : q.den.factorization p ≤ k) :
    ∃ m : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = m := by
  have hp : p.Prime := Fact.out
  have hN : 0 < D * p ^ k := Nat.mul_pos hD (pow_pos hp.pos k)
  have hdvd : q.den ∣ D * p ^ k := by
    rw [← Nat.factorization_le_iff_dvd q.den_nz hN.ne']
    intro ℓ
    rw [Nat.factorization_mul hD.ne' (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow, hp.factorization]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases hl : ℓ = p
    · subst hl; simp only [Finsupp.single_eq_same, mul_one]; have := h2; omega
    · have := h1 ℓ hl; omega
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c * q.num, ?_⟩
  rw [hc]
  calc ((q.den * c : ℕ) : ℚ) * q = (c : ℚ) * (q * q.den) := by push_cast; ring
    _ = _ := by rw [Rat.mul_den_eq_num]; push_cast; ring

theorem grp_val_injective (G : HTGroup p) (β : G.Cˣ) :
    Function.Injective (fun y : grp G β => (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
  intro y y' hyy
  have hu : (y : G.Cˣ × ℚˣ).1 = (y' : G.Cˣ × ℚˣ).1 := Units.ext hyy
  have h1 : (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y.2.1
  have h2 : (((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * β * sh G ((y' : G.Cˣ × ℚˣ).1 : G.Cˣ) =
      algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * β := y'.2.1
  rw [hu] at h1
  have h3 : algebraMap ℚ G.C (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = algebraMap ℚ G.C (((y' : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := by
    have := h1.symm.trans h2
    simpa using congrArg (· * ((β⁻¹ : G.Cˣ) : G.C)) this
  have h4 : (y : G.Cˣ × ℚˣ).2 = (y' : G.Cˣ × ℚˣ).2 := Units.ext ((algebraMap ℚ G.C).injective h3)
  exact Subtype.ext (Prod.ext hu h4)

theorem finite_fix_core (G : HTGroup p) (hG : G.a = 1) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) (hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f')
    (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (hsym : sh G β = β)
    (hR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) (h : G.GAf × Gr G 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re) :
    Set.Finite {y : grp G β | FixL G v β y z ∧
      f (h.1⁻¹ * toAfF G β x t hx y * h.1) * f' (h.2⁻¹ * toP1 G β y * h.2) ≠ 0} := by
  obtain ⟨D, hD, hAf⟩ := GlobalTheory.T.formGroup_testFunction_support_bounded_denominators p G β x t hx L f hf h.1
  obtain ⟨k, hP⟩ := GlobalTheory.T.p_adic_denominator_bound p G β K' f' hf' h.2
  obtain ⟨K, hK⟩ := GlobalTheory.T.fixed_vector_squared_bound p G hG v hv β hsym hR z hz
  set N : ℕ := D * p ^ k with hN
  have hNpos : (0 : ℝ) < N := by
    rw [hN]; exact_mod_cast Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)
  set b := Module.finBasis ℚ G.C with hb
  set S : Finset G.C := Finset.univ.image (fun i => ((N : ℚ)⁻¹) • b i) with hS
  let Φ : G.C →+ (InfinitePlace G.F → Fin G.n → Fin G.n → ℂ) :=
    AddMonoidHom.mk' (fun c w i l => G.psi w c i l) (by intro a c; funext w i l; simp [map_add (f := _)])
  refine Set.Finite.of_finite_image ?_ ((grp_val_injective G β).injOn)
  refine GlobalTheory.T.finite_of_bounded_image_in_finitely_generated_subgroup Φ (fun k e he => GlobalTheory.T.embeddings_real_independent p G k e he) S _ ?_ (Real.sqrt (max K 0 * N)) ?_
  · rintro _ ⟨y, ⟨-, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    show (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) ∈ AddSubgroup.closure (S : Set G.C)
    rw [← b.sum_repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    have hN0 : (N : ℚ) ≠ 0 := by
      rw [hN]; exact_mod_cast (Nat.mul_pos hD (pow_pos (Fact.out : p.Prime).pos k)).ne'
    have e : b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i • b i = m • ((N : ℚ)⁻¹ • b i) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, ← hm, mul_comm, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
    rw [e]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (by
      simp only [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact ⟨i, rfl⟩)) m
  · rintro _ ⟨y, ⟨hfix, hne⟩, rfl⟩
    have hf1 := left_ne_zero_of_mul hne
    have hf2 := right_ne_zero_of_mul hne
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := exists_int_of_den_le D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hNpos) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
        calc (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) = 1 * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := (one_mul _).symm
          _ ≤ ((N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹) * (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) :=
            mul_le_mul_of_nonneg_right h2 hs.le
          _ = N := by field_simp
      exact_mod_cast this
    have hsR : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by exact_mod_cast hs
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    have h1 := hK y hfix w i j
    have h2 : ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ max K 0 * N :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_max_left K 0) hsR.le).trans
        (mul_le_mul_of_nonneg_left hsN (le_max_right K 0)))
    have h3 := Real.abs_le_sqrt h2
    rwa [abs_of_nonneg (norm_nonneg _)] at h3

end GlobalTheory.FinFix
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.minpoly_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  first | (exact @GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (exact GlobalTheory.FinPtsAway.exists_den_minpoly_coeff) | (intros; apply GlobalTheory.FinPtsAway.exists_den_minpoly_coeff  <;> assumption)
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.definitePair_term_eq_centraliser_orbit_sum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : GlobalTheory.LKDef.DPair G) (hm : (P.γ, P.c) ∈ GlobalTheory.LKCx.grp G P.β)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      P.term L.K.toSubgroup f 1 K' f' =
        centSum (GlobalTheory.LKCx.toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec)
          (GlobalTheory.LKCx.toP1 G P.β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' ⟨(P.γ, P.c), hm⟩ := by
  first | exact @GlobalTheory.LKDef.TermPair.term_eq_centSum | exact GlobalTheory.LKDef.TermPair.term_eq_centSum | (intros; apply GlobalTheory.LKDef.TermPair.term_eq_centSum <;> assumption)
end
