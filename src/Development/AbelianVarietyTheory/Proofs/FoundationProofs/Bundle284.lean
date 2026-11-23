module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvarianceImpliesCongruence
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle077
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle221
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle216
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept

@[expose] public section

section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.siegel_invariance_implies_congruence : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ) (γ : SL(2, ℤ)), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → (∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) → X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) → γ ∈ CongruenceSubgroup.Gamma M ∨ -γ ∈ CongruenceSubgroup.Gamma M := by
  first | exact @GlobalTheory.SiegSep.fix_siegel_pm_one | exact GlobalTheory.SiegSep.fix_siegel_pm_one | (intros; apply GlobalTheory.SiegSep.fix_siegel_pm_one <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.AdeleCMSplit


open scoped TensorProduct NNReal Matrix in
open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Eis.Conv.AdeleCMSplit.exists_adele_split : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∃ e : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) ≃+* (InfinitePlace E → ℂ) × FiniteAdeleRing (𝓞 E) E,
      Continuous e.symm ∧
      (∀ x : E, e (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) =
        (fun w : InfinitePlace E => w.embedding x, algebraMap E (FiniteAdeleRing (𝓞 E) E) x)) ∧
      e (_root_.GlobalTheory.Eis.Conv.halfE F E).1 = (fun _ => 2⁻¹, 1) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨e₁, he₁, -, he₁s⟩ := _root_.GlobalTheory.AdSplit.exists_adele_equiv F E
  choose θ hθ using fun τ => (_root_.GlobalTheory.Mem.VolEmb.existsUnique_infEmb F E σ hσ τ).exists
  have hcm : _root_.GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace E => w.embedding) := by
    unfold _root_.GlobalTheory.Mem.Vol.IsCMFam
    simp only [InfinitePlace.mk_embedding]
    exact Function.bijective_id
  obtain ⟨e₂, he₂, -, he₂s, -⟩ := _root_.GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ
    (InfinitePlace E) (fun w => w.embedding) (fun w => θ w.embedding) hσ hcm (fun w => hθ _)
  obtain ⟨ι, hι1, hι2, -⟩ := _root_.GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιs := _root_.GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  refine ⟨e₁.trans (RingEquiv.prodCongr e₂ ι), ?_, ?_, ?_⟩
  · exact he₁s.comp ((he₂s.comp continuous_fst).prodMk (hιs.comp continuous_snd))
  · intro x
    have h1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x = (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x := rfl
    have h2 : e₁ ((1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] x) =
        ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x, (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]; exact Algebra.TensorProduct.map_tmul _ _ _ _
      · rw [(he₁ _).2]; exact Algebra.TensorProduct.map_tmul _ _ _ _
    rw [h1, RingEquiv.trans_apply, h2]
    refine Prod.ext ?_ ?_
    · funext w
      exact (he₂ _ w).trans ((hθ _).1 x)
    · exact hι1 x
  · have h0 : ((_root_.GlobalTheory.Eis.Conv.halfE F E).1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E) =
        ((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)
          ⊗ₜ[F] (1 : E) := rfl
    have h2 : e₁ (((algebraMap F (InfiniteAdeleRing F) 2⁻¹, (1 : FiniteAdeleRing (𝓞 F) F)) :
        _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ⊗ₜ[F] (1 : E)) = ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹, 1) := by
      refine Prod.ext ?_ ?_
      · rw [(he₁ _).1]
        refine (Algebra.TensorProduct.map_tmul _ _ _ _).trans ?_
        show algebraMap F (InfiniteAdeleRing F) 2⁻¹ ⊗ₜ[F] (1 : E) = _
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
      · rw [(he₁ _).2]; exact (Algebra.TensorProduct.map_tmul _ _ _ _).trans (by rfl)
    rw [h0]
    refine (congrArg (RingEquiv.prodCongr e₂ ι) h2).trans ?_
    refine Prod.ext ?_ ?_
    · funext w
      refine ((he₂ ((1 : InfiniteAdeleRing F) ⊗ₜ[F] algebraMap F E 2⁻¹) w).trans
        ((hθ _).1 _)).trans ?_
      simp only [map_inv₀, map_ofNat]
    · exact map_one ι

end GlobalTheory.Eis.Conv.AdeleCMSplit
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

namespace GlobalTheory.Eis.Conv.Discr

open Filter Topology

section Abstract

variable {A E : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [Field E]
  (ι : E →+* A)

theorem finite_of_isCompact (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0) {Ω : Set A}
    (hΩ : IsCompact Ω) : {x : E | ι x ∈ Ω}.Finite := by
  obtain ⟨U, hU, hx⟩ := h
  refine hΩ.induction_on (p := fun s => {x : E | ι x ∈ s}.Finite) (by simp)
    (fun s t hst ht => ht.subset fun x hx => hst hx)
    (fun s t hs ht => (hs.union ht).subset fun x hx => hx) fun a _ => ?_
  have hc : ContinuousAt (fun p : A × A => p.1 - p.2) (a, a) := by fun_prop
  have h1 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 (a, a) :=
    hc.preimage_mem_nhds (by simpa using hU)
  rw [nhds_prod_eq, Filter.mem_prod_self_iff] at h1
  obtain ⟨V, hV, hVU⟩ := h1
  refine ⟨V, mem_nhdsWithin_of_mem_nhds hV, Set.Subsingleton.finite fun x hx' y hy => ?_⟩
  refine sub_eq_zero.1 (hx _ ?_)
  rw [map_sub]
  exact hVU (Set.mk_mem_prod hx' hy)

theorem eventually_eq_zero [T2Space A] (h : ∃ U ∈ 𝓝 (0 : A), ∀ x : E, ι x ∈ U → x = 0)
    {Ω : Set A} (hΩ : IsCompact Ω) {s ε : A} (hs : Tendsto (fun m : ℕ => s ^ m) atTop (𝓝 ε))
    (hε : ¬ IsUnit ε) :
    ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, ι x = s ^ m * ω → x = 0 := by
  have hK : IsCompact ((fun p : A × A => p.1 * p.2) ''
      (insert ε (Set.range fun m : ℕ => s ^ m) ×ˢ Ω)) :=
    (hs.isCompact_insert_range.prod hΩ).image (by fun_prop)
  have hfin := finite_of_isCompact ι h hK
  have hev : ∀ x : E, ∀ᶠ m : ℕ in atTop, ∀ ω ∈ Ω, ι x = s ^ m * ω → x = 0 := by
    intro x
    by_cases hx : x = 0
    · exact Eventually.of_forall fun _ _ _ _ => hx
    have h1 : ∀ᶠ t in 𝓝 ε, ∀ ω ∈ Ω, ι x ≠ t * ω := by
      refine hΩ.eventually_forall_of_forall_eventually (P := fun t ω => ι x ≠ t * ω)
        fun ω _ => ?_
      have ho : IsOpen {p : A × A | ι x ≠ p.1 * p.2} :=
        isOpen_ne_fun continuous_const (by fun_prop)
      refine ho.mem_nhds fun he => hε ?_
      have hu : IsUnit (ε * ω) := by
        have := (IsUnit.mk0 x hx).map ι
        rwa [he] at this
      exact isUnit_of_mul_isUnit_left hu
    filter_upwards [hs.eventually h1] with m hm ω hω he
    exact absurd he (hm ω hω)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 ((eventually_all_finite hfin).2 fun x _ => hev x)
  refine ⟨m₀, fun m hm ω hω x hx => hm₀ m hm x ?_ ω hω hx⟩
  exact ⟨(s ^ m, ω), ⟨Or.inr ⟨m, rfl⟩, hω⟩, hx.symm⟩

end Abstract

theorem tendsto_halfInf_pow (F : Type) [Field F] [NumberField F] :
    Tendsto (fun m : ℕ => (halfInf F).1 ^ m) atTop (𝓝 ((0, 1) : AF F)) := by
  have h1 : Tendsto (fun m : ℕ => (algebraMap F (Ainf F) 2⁻¹) ^ m) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    have h : ‖algebraMap F (Ainf F) 2⁻¹ v‖ < 1 := by
      rw [InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.norm_coe]
      change v (2⁻¹ : F) < 1
      rw [← InfinitePlace.norm_embedding_eq, map_inv₀, map_ofNat, norm_inv]
      norm_num
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
  have h2 : Tendsto (fun m : ℕ => (1 : FiniteAdeleRing (𝓞 F) F) ^ m) atTop (𝓝 1) := by
    simp only [one_pow]
    exact tendsto_const_nhds
  exact h1.prodMk_nhds h2

theorem finite_and_eventually_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Ω : Set (AF F ⊗[F] E)), IsCompact Ω → {x : E | inclR (F := F) (AF F) x ∈ Ω}.Finite ∧ ∃ m₀ : ℕ, ∀ m, m₀ ≤ m → ∀ ω ∈ Ω, ∀ x : E, inclR (F := F) (AF F) x = (halfE F E).1 ^ m * ω → x = 0 := by
  intro F E _ _ _ _ _ Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have h := GlobalTheory.AdelicMatrixLattice.discrete_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F)
  refine ⟨finite_of_isCompact _ h hΩ, eventually_eq_zero _ h hΩ
    (ε := algebraMap (AF F) (AF F ⊗[F] E) (0, 1)) ?_ fun hu => ?_⟩
  · have hc : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
    have := (hc.tendsto _).comp (tendsto_halfInf_pow F)
    refine this.congr fun m => ?_
    exact map_pow (algebraMap (AF F) (AF F ⊗[F] E)) _ m
  · have h0 : algebraMap (AF F) (AF F ⊗[F] E) (0, 1) * algebraMap (AF F) (AF F ⊗[F] E) (1, 0) = 0 := by
      refine (map_mul (algebraMap (AF F) (AF F ⊗[F] E)) _ _).symm.trans ?_
      refine (congrArg (algebraMap (AF F) (AF F ⊗[F] E)) ?_).trans (map_zero _)
      exact Prod.ext (zero_mul _) (mul_zero _)
    have h1 := hu.mul_right_eq_zero.1 h0
    have hinj : Function.Injective (algebraMap (AF F) (AF F ⊗[F] E)) :=
      Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
    have h2 : ((1, 0) : AF F) = 0 := hinj (h1.trans (map_zero _).symm)
    obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h3 : (1 : v.Completion) = 0 := congrFun (congrArg Prod.fst h2) v
    exact one_ne_zero h3

end GlobalTheory.Eis.Conv.Discr
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl

variable {p : ℕ} [Fact p.Prime]

theorem norm_lamC_root_mul (lam : Qbar →+* ℂ_[p]) {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1)
    (x : ℂ) : ‖lamC lam (ζ * x)‖ = ‖lamC lam x‖ := by
  have hq : ζ ∈ Qbar := by
    refine mem_algebraicClosure_iff.2 ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.X_pow_sub_C_ne_zero hn 1, ?_⟩
    simp [hζ]
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hζ
    exact zero_ne_one hζ
  have h1 : ‖lam ⟨ζ, hq⟩‖ = 1 := by
    have e : (⟨ζ, hq⟩ : Qbar) ^ n = 1 := Subtype.ext (by simpa using hζ)
    have : ‖lam ⟨ζ, hq⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  by_cases hx : x ∈ Qbar
  · have hzx : ζ * x ∈ Qbar := mul_mem hq hx
    simp only [lamC, dif_pos hx, dif_pos hzx]
    have : (⟨ζ * x, hzx⟩ : Qbar) = ⟨ζ, hq⟩ * ⟨x, hx⟩ := rfl
    rw [this, map_mul, norm_mul, h1, one_mul]
  · have hzx : ζ * x ∉ Qbar := by
      intro h
      apply hx
      have : x = ζ⁻¹ * (ζ * x) := by field_simp
      rw [this]
      exact mul_mem (inv_mem hq) h
    simp only [lamC, dif_neg hx, dif_neg hzx]

theorem cval_norm_periodic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t ω : ℂ, InRationalLattice g.abelian₂ t → ω ∈ g.abelian₂ → ‖GlobalTheory.ThetaTransl.cval g (t + ω)‖ = ‖GlobalTheory.ThetaTransl.cval g t‖ := by
  intro D p _ cc δ g hg t ω ht hω
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg
  have hlat := (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ ⟨hcc, hδ⟩).1
  rw [← hΛ] at hlat
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ hlat
  have hlaw := (GlobalTheory.OddTheta.sgStar_laws g.abelian₂ hlat).1.2.2.2 ω hω t
  obtain ⟨m, hm, hmt⟩ := ht
  set s := sgStar g.abelian₂ with hs
  set A : ℂ := (area g.abelian₂ : ℂ) with hAdef
  have hA : area g.abelian₂ = GlobalTheory.latticeArea L := GlobalTheory.OddTheta.area_eq L g.abelian₂ hL
  have hA0 : A ≠ 0 := by
    rw [hAdef, hA]; exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
  set ψ : ℂ := if ω / 2 ∈ g.abelian₂ then 1 else -1 with hψ
  set E : ℂ := Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) with hE
  have key : U1 g.abelian₂ (t + ω) s 0 = (ψ * E) * U1 g.abelian₂ t s 0 := by
    have h2 : s (t + ω) = ψ * s t * Complex.exp (-(-(Real.pi : ℂ) * t * (starRingEnd ℂ) ω / A -
        (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A))) := by
      have hlaw' := hlaw
      simp only [U1] at hlaw'
      rw [← hlaw', mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
    simp only [U1]
    rw [zero_add, zero_add, h2, show ψ * E * (s t * Complex.exp (-(Real.pi : ℂ) * 0 * (starRingEnd ℂ) t / A -
        (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) = ψ * s t * (E * Complex.exp (-(Real.pi : ℂ) * 0 *
        (starRingEnd ℂ) t / A - (Real.pi : ℂ) * t * (starRingEnd ℂ) t / (2 * A))) by ring,
      hE, ← Complex.exp_add, mul_assoc (ψ * s t), ← Complex.exp_add]
    congr 1
    congr 1
    simp only [map_add (f := _)]
    ring
  have hroot : (ψ * E) ^ (2 * m) = 1 := by
    have hψ2 : ψ ^ 2 = 1 := by rw [hψ]; split_ifs <;> norm_num
    have ha' : (m : ℂ) * t ∈ L.lattice := (hL _).1 hmt
    have hω' : ω ∈ L.lattice := (hL _).1 hω
    obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ha' hω'
    have hL0 : (GlobalTheory.latticeArea L : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.latticeArea_pos L).ne'
    have him : ((m : ℂ) * t * (starRingEnd ℂ) ω).im = k * GlobalTheory.latticeArea L := by
      rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff (GlobalTheory.latticeArea_pos L).ne'] at hk
      exact hk
    have hc : (starRingEnd ℂ) ((m : ℂ) * t * (starRingEnd ℂ) ω) = (m : ℂ) * (starRingEnd ℂ) t * ω := by
      simp [map_mul]
    have hsub := Complex.sub_conj ((m : ℂ) * t * (starRingEnd ℂ) ω)
    rw [hc, him] at hsub
    have hexp : ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A)) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      calc ((2 * m : ℕ) : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) ω - ω * (starRingEnd ℂ) t) / (2 * A))
          = (Real.pi : ℂ) * ((m : ℂ) * t * (starRingEnd ℂ) ω - (m : ℂ) * (starRingEnd ℂ) t * ω) / A := by
            push_cast; field_simp
        _ = (Real.pi : ℂ) * (((2 * (k * GlobalTheory.latticeArea L) : ℝ) : ℂ) * Complex.I) / A := by rw [hsub]
        _ = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
            rw [hAdef, hA]; push_cast; field_simp
    rw [mul_pow, pow_mul, hψ2, one_pow, one_mul, hE, ← Complex.exp_nat_mul, hexp,
      Complex.exp_int_mul_two_pi_mul_I]
  unfold cval
  rw [key]
  exact norm_lamC_root_mul g.lam (by omega) hroot _

end GlobalTheory.ThetaTransl
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaStab

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  exact h2 ▸ (h1 1).1

theorem mem_standardThetaLattice_iff_adelicIdeal (hcc : cc ≠ ⊥) (x : VC D N N') : x ∈ La0 D (tor0 D cc δ) N N' ↔
    ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, inc D (z i j) ∈ IhE D cc := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hx
    obtain ⟨z, hz, h⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') x hx
    exact ⟨z, hz, fun i j => by simpa using h i j⟩
  · rintro ⟨z, rfl, h⟩
    exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') z (fun i j => by simpa using h i j)

theorem inc_mem_of_isIntegral {e : D.host.E} (he : IsIntegral ℤ e) : inc D e ∈ OhE D :=
  GlobalTheory.NormSum.MovedTheta.inc_int (⟨e, he⟩ : 𝓞 D.host.E)

theorem mulV_mem (hcc : cc ≠ ⊥) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (h' : ∀ i j, IsIntegral ℤ (M' i j)) (h : ∀ i j, IsIntegral ℤ (M i j)) (x : VC D N N')
    (hx : x ∈ La0 D (tor0 D cc δ) N N') : mulV D M' M x ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
  refine (mem_standardThetaLattice_iff_adelicIdeal hcc _).2 ⟨_, mulV_pt D cc δ M' M z, fun i j => ?_⟩

  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun k _ => ?_
  rw [mul_comm]
  refine MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h k j)) (sum_mem fun l _ => ?_)
  exact MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h' i l)) (hz l k)

theorem exists_denom {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, IsIntegral ℤ ((m • M) i j) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h (M i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, ← natCast_zsmul]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h1
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', neg_smul]; exact h1.neg

theorem mulV_nsmul (m' m : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (x : VC D N N') : mulV D (m' • M') (m • M) x = (m' * m) • mulV D M' M x := by
  funext τ
  have e : ∀ {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) D.host.E),
      (k • A).map (embT D τ) = k • A.map (embT D τ) := by
    intro n k A
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
  change (m' • M').map (embT D τ) * Matrix.of (x τ) * (m • M).map (embT D τ) =
    (m' * m) • (M'.map (embT D τ) * Matrix.of (x τ) * M.map (embT D τ))
  rw [e, e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, mul_smul]

theorem inv_eq_adj {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    (((g : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = (adj D γ).map (inc D) := by
  have h1 : γ * adj D γ = 1 := (GlobalTheory.NormSum.mem_ratG_intG D n).2.2.2.1 g γ h
  apply Units.inv_eq_of_mul_eq_one_right
  unfold IsRat at h
  rw [h, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_iff_moved (hcc : cc ≠ ⊥) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : IsRat D (γA : GL (Fin N) (AE D)) γ)
    (h' : IsRat D (γA' : GL (Fin N') (AE D)) γ') (hL : Moves D (γA : GL (Fin N) (AE D)) L₁)
    (hL' : Moves D (γA' : GL (Fin N') (AE D)) L₁') (x : VC D N N') :
    x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have h1 : adj D γ * γ = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ h)
  have h1' : adj D γ' * γ' = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' h')
  have key : ∀ z : Matrix (Fin N') (Fin N) D.host.E,
      (((γA' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = (adj D γ' * z * γ).map (inc D) := by
    intro z
    have h2 := h
    unfold IsRat at h2
    rw [inv_eq_adj h', h2, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro hx
    obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
    rw [mulV_pt]
    refine GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' γA γA' _ _ hL hL' _ fun i j => ?_
    have e : adj D γ' * (γ' * z * adj D γ) * γ = z := by
      rw [Matrix.mul_assoc γ', ← Matrix.mul_assoc (adj D γ'), h1', Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rw [key, e]
    exact hz i j
  · intro hx
    obtain ⟨w, hw, hz⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' γA γA' _ _ hL hL' _ hx
    refine (mem_standardThetaLattice_iff_adelicIdeal hcc x).2 ⟨adj D γ' * w * γ, ?_, fun i j => ?_⟩
    · rw [← mulV_pt, ← hw, mulV_mulV, h1, h1', mulV_one]
    · have := hz i j
      rw [key] at this
      exact this

end GlobalTheory.ThetaStab


open GlobalTheory.ThetaStab in
theorem GlobalTheory.ThetaStab.mulV_theta_lattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  refine ⟨fun M' M h' h x hx => mulV_mem hcc M' M h' h x hx, fun M' M => ?_,
    fun γA γA' γ γ' L₁ L₁' h h' hL hL' x => mem_iff_moved hcc γA γA' γ γ' L₁ L₁' h h' hL hL' x⟩
  obtain ⟨m', hm', h'⟩ := exists_denom M'
  obtain ⟨m, hm, h⟩ := exists_denom M
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun x hx => ?_⟩
  rw [← mulV_nsmul]
  exact mulV_mem hcc _ _ h' h x hx
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.sigmaStarSquareQuotient_in_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  first | exact @GlobalTheory.EvenTheta.Param.sqTh_atU | exact GlobalTheory.EvenTheta.Param.sqTh_atU | (intros; apply GlobalTheory.EvenTheta.Param.sqTh_atU <;> assumption)
end
