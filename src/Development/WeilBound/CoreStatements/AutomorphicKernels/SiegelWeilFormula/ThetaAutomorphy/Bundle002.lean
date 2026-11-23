module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ContinuousMhUInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ExistsLth
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.PiInfInclR
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
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

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_meanAdm (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar) (hT : TTheta) (d : SD σ) :
    ∃ Λ ∈ (adeleClass F).adm d.κ, ∀ Ψ ∈ d.sch,
      Λ Ψ = (d.μ.real d.D)⁻¹ • ∫ g in d.D, thetaSum F (d.S g Ψ) ∂d.μ := by
  obtain ⟨l, hl, hlθ⟩ := exists_lth d
  have hpres : ∀ g, ∀ Ψ ∈ d.sch, d.S g Ψ ∈ d.sch := fun g Ψ hΨ => d.ok.dbl.lin.pres g Ψ hΨ
  have hfun : ∀ Ψ ∈ d.sch, (fun g => l (d.S g Ψ)) = fun g => thetaSum F (d.S g Ψ) :=
    fun Ψ hΨ => funext fun g => hlθ _ (hpres g Ψ hΨ)
  have hint : ∀ Ψ ∈ d.sch, IntegrableOn (fun g => l (d.S g Ψ)) d.D d.μ := fun Ψ hΨ => by
    rw [hfun Ψ hΨ]; exact intOn_S hS hP hT d hΨ
  set c : ℝ := (d.μ.real d.D)⁻¹ with hc
  let L0 : d.sch →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => c • ∫ g in d.D, l (d.S g Ψ.1) ∂d.μ
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, map_add (f := _)]
        rw [integral_add (hint _ Ψ.2) (hint _ Ψ'.2), smul_add]
      map_smul' := fun a Ψ => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul, mul_smul_comm] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L0
  have hΛv : ∀ Ψ (hΨ : Ψ ∈ d.sch), Λ Ψ = c • ∫ g in d.D, l (d.S g Ψ) ∂d.μ := fun Ψ hΨ => by
    have := congrArg (fun L => L ⟨Ψ, hΨ⟩) hΛ
    simpa [L0] using this
  refine ⟨Λ, fun gf hgf => ?_, fun Ψ hΨ => by rw [hΛv Ψ hΨ, hfun Ψ hΨ]⟩
  choose Th hTh using fun h : UA σ d.A.J => d.ok.dbl.lin.adm h l hl gf hgf
  have hmem : ∀ f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f gf ∈ d.sch :=
    fun f => Submodule.subset_span ⟨f, gf, hgf, rfl⟩
  have hTv : ∀ h f, Th h f = thetaSum F (d.S h (pureA F f gf)) := fun h f => by
    rw [← hTh h f, LinearMap.comp_apply, hlθ _ (hpres h _ (hmem f))]
  haveI : BarrelledSpace ℂ (SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ) := GlobalTheory.T.schwartzMap_barrelledSpace' _
  have hUE : UniformEquicontinuous ((↑) ∘ Th) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun _ f => by
    obtain ⟨C, hC⟩ := bdd_S hS hP hT d (hmem f)
    refine ⟨C, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa [hTv] using hC h
  have hpa : ∀ f f' : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') gf = pureA F f gf + pureA F f' gf := fun f f' => funext fun x => by
    simp [pureA, add_mul]
  have hps : ∀ (a : ℂ) (f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) gf = a • pureA F f gf := fun a f => funext fun x => by
    simp [pureA, mul_assoc]
  let Lf : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ (pureA F f gf)
      map_add' := fun f f' => by rw [hpa, map_add (f := _)]
      map_smul' := fun a f => by rw [hps, map_smul]; rfl }
  have hLf : ∀ f, Lf f = c • ∫ g in d.D, Th g f ∂d.μ := fun f => by
    show Λ (pureA F f gf) = _
    rw [hΛv _ (hmem f)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show l (d.S g (pureA F f gf)) = Th g f
    rw [← hTh g f]; rfl
  have hfin : d.μ d.D < ⊤ := (cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom
  have hpos : 0 < d.μ.real d.D := by
    haveI := (cpt hS d).cnt
    haveI := d.ok.haar
    exact ENNReal.toReal_pos (fd_ne d.ok.dom) hfin.ne
  have hcont : Continuous Lf := by
    refine continuous_of_continuousAt_zero Lf.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.1 (hUE.equicontinuous 0)) (ε / 2) (half_pos hε)] with f hf
    rw [dist_zero_right]
    show ‖Lf f‖ < ε
    rw [hLf]
    have hb : ∀ g ∈ d.D, ‖Th g f‖ ≤ ε / 2 := fun g _ => by
      have := (hf g).le
      simpa [dist_comm] using this
    calc ‖c • ∫ g in d.D, Th g f ∂d.μ‖ ≤ c * (ε / 2 * d.μ.real d.D) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin hb
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := half_lt_self hε
  exact ⟨⟨Lf, hcont⟩, fun f => rfl⟩

end PositivityTheory.SiegelWeilFormula.Tauto

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}



theorem stepA (hP : TPar) (hT : TTheta) (d : SD σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G}
    (hnb : IsNMap (σ := σ) (Y := d.Y) d.b nb) (x : d.G) (β : nA σ d.Y d.b) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (tr d g X) := by
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl

theorem meas_tr (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    AEMeasurable (fun g => ‖f (tr d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((cont_tr d hf X).enorm.measurable).aemeasurable

theorem tbdd (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (tr d g X)‖) ∧ ∑' X, ‖f (tr d g X)‖ ≤ K := by
  open Kdil.Tb in
  obtain ⟨Ω, hΩ, cov⟩ := (cpt hS d).cov
  obtain ⟨u, hu, hb⟩ := bound_cpt d f hf Ω hΩ
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h
  obtain ⟨e, he⟩ := reindex d f γ hγ
  have key : (fun X => ‖f (mat h⁻¹ * incM F X)‖) = (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖) ∘ e := by
    funext X
    exact congrArg norm (he h X).symm
  have hs : Summable (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
  change Summable (fun X => ‖f (mat h⁻¹ * incM F X)‖) ∧
    ∑' X, ‖f (mat h⁻¹ * incM F X)‖ ≤ ∑' ξ, u ξ
  refine ⟨?_, ?_⟩
  · rw [key]; exact e.summable_iff.2 hs
  · rw [key]
    show ∑' X, ‖f (mat (γ * h)⁻¹ * incM F (e X))‖ ≤ _
    rw [e.tsum_eq (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖)]
    calc ∑' Y, ‖f (mat (γ * h)⁻¹ * incM F Y)‖ ≤ ∑' Y, u (xi d Y) :=
          hs.tsum_le_tsum (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
      _ = ∑' ξ, u ξ := (xi d).tsum_eq u

theorem pt_bdd (d : SD σ) {f : Mx F E d.m d.n → ℂ} (g : UA σ d.A.J) (s : Set (Matrix (Fin d.m) (Fin d.n) E)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (tr d g X)‖)) (hle : ∑' X, ‖f (tr d g X)‖ ≤ K) :
    ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ∑' X, ‖f (tr d g X)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (tr d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (tr d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (tr d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle

theorem lint_fin (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    (s : Set (Matrix (Fin d.m) (Fin d.n) E)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (tr d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  haveI := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := tbdd hS d hf
  have hfin : d.μ d.D < ⊤ := (cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (tr d g X.1)‖ₑ) fun X => meas_tr d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => pt_bdd d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)

theorem lint_fin_all (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := lint_fin hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ)] at this

theorem continuous_tt (d : SD σ) : Continuous (d.tt) := by
  have h1 : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)

theorem thetaCoef_at (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) (d : SD σ)
    {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ) := by
  haveI := countable_mat (E := E) d.m d.n
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hf : d.T (d.om x Φ) ∈ d.schM := (hB F E σ d).1 _ hΨ
  have hen : ∀ a, ‖d.B.ψ a‖ₑ = 1 := fun a => by
    rw [← ofReal_norm_eq_enorm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]
  have hψc : Continuous d.B.ψ := d.std.1
  set f : Mx F E d.m d.n → ℂ := d.T (d.om x Φ) with hfdef
  set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef
  set G : Matrix (Fin d.m) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AE F E) :=
    fun X => d.gram (incM F X) (incM F X) with hG
  set e : nA σ d.Y d.b → Matrix (Fin d.m) (Fin d.n) E → ℂ :=
    fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ
  set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (tr d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (tr d g X)) (d.μ.restrict d.D) :=
    fun X => (cont_tr d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : nA σ d.Y d.b => β.1 := continuous_subtype_val
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((continuous_tt d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((continuous_tt d).comp (continuous_const.matrix_mul hcb)).neg)

  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (tr d g X) :=
      fun g => stepA hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (tr d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, enorm_mul, hen, one_mul] using lint_fin_all hS d hf

  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := gram_mem d X T
    simp only [he, hχ, chr_comb]
    rw [orth d hc _ hm ⟨S₀, hS₀⟩]
    simp only [half_eq_iff]
    rfl

  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, SD.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (lint_fin_all hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)
    exact enorm_integral_le_lintegral_enorm _
  have h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X =
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]
    exact tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
  have h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E //
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    haveI : Countable {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} :=
      Subtype.countable
    show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)),
      f (tr d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g =>
      f (tr d g X.1)) (fun X => hmeas X.1) (lint_fin hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]

theorem thetaCoef (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) : ThetaCoef :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => thetaCoef_at hS hB hP hT d hΦ hc T x

end PositivityTheory.SiegelWeilFormula.Tauto

end
end
