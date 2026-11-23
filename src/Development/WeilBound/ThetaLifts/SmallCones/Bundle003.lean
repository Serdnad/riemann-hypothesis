module

public import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import GroundTheory.GlobalFields.TateThesis.Bundle007
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
public import GroundTheory.GlobalFields.TateThesis.GlobalZeta
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.WeilBound.ThetaLifts.CTKernel
import Development.WeilBound.ThetaLifts.TowerModels.Bundle003

@[expose] public section

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def LinEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      ∀ x u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → x.map (piW t) = 0 → evFin F v (sy σ X W x u) =
        ((X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ)ᵀ * u.map (piW t)).trace

def SoZeroA' : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₀.IsGood B.ψ → ∀ M₁ : Model σ X W₁, M₁.IsGood B.ψ →
    (∃ χX χW om₁ om₀ r₁ s₁ r₀ s₀ r₂ s₂, IsPair B M₁ χX χW om₁ r₁ s₁ r₂ s₂ ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₂ s₂) →
    ∀ e₀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ Ψ ∈ schA F _,
      e₀ Ψ ∈ M₁.So B.ψ B.τ₁ → e Ψ = 0

end PositivityTheory.ThKCT

end
end

section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def StabDec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧ (p ∈ ratU σ Y.J → g₁ ∈ ratU σ Y₁.J)) ∧
    (∀ (ξ : Eˣ), ∀ g₁ ∈ ratU σ Y₁.J, ∀ m, IsLevi H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁ m → m ∈ ratU σ Y.J) ∧
    ∀ t (g₁ : UA σ Y₁.J) m, IsLevi H t g₁ m → ∀ u ∈ unip σ Y H, m⁻¹ * u * m ∈ unip σ Y H

def ConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftA H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁

def ConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁

end PositivityTheory.ThKCT

end
end

section

noncomputable section

open NumberField MeasureTheory GroundTheory.Global nonZeroDivisors in
theorem PositivityTheory.ThKCT.Tate.transport {K G : Type} [Field K] [NumberField K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (e : G ≃ₜ* IdeleGroup K) (μ : Measure G) [μ.IsHaarMeasure] {z : ℝ} (hz : 1 < z) {k : ℕ}
    (hk : 2 * z + 2 < k) (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∫⁻ l, ENNReal.ofReal (infiniteZetaBound z k (IdeleGroup.toInfinite K (e l)) *
      finiteZetaBound L z (IdeleGroup.toFinite K (e l))) ∂μ < ⊤ := by
  have h2 := (integrable_zetaBound (K := K) hz hk L).smul_measure_nnreal (c := (μ.map e).haarScalarFactor (ideleMeasure K))
  rw [← Measure.isMulLeftInvariant_eq_smul] at h2
  exact (h2.comp_measurable e.continuous.measurable).lintegral_lt_top

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

namespace Tate

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F E) in
abbrev Φ : AE F E ≃ₐ[AF F] AdeleRing (𝓞 E) E := adeleTensorAlgEquivLeft F E

theorem cont_Φ : Continuous (Φ F E) := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).toLinearMap

theorem cont_Φ_symm : Continuous (Φ F E).symm := by
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := (ideleTop F E).1.1
  exact IsModuleTopology.continuous_of_linearMap (Φ F E).symm.toLinearMap


variable (F E) in
def Ψ : (AE F E)ˣ ≃ₜ* IdeleGroup E where
  toMulEquiv := Units.mapEquiv (Φ F E).toMulEquiv
  continuous_toFun := Continuous.units_map (Φ F E).toMulEquiv.toMonoidHom cont_Φ
  continuous_invFun := Continuous.units_map (Φ F E).symm.toMulEquiv.toMonoidHom cont_Φ_symm

theorem Ψ_val (l : (AE F E)ˣ) : ((Ψ F E l : IdeleGroup E) : AdeleRing (𝓞 E) E) = Φ F E l := rfl

theorem absE_eq (l : (AE F E)ˣ) : (absE F E l : ℝ) = IdeleGroup.ideleModule E (Ψ F E l) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), IdeleGroup.ideleModule_apply, IdeleGroup.infiniteModule,
    IdeleGroup.finiteModule, coe_ideleNorm, Ψ_val, Algebra.norm_eq_of_algEquiv, GlobalTheory.Doubling.absE_apply, NNReal.coe_mul,
    NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_unitInf, NNReal.coe_pow]
    rfl
  · rw [show ((∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v l) : ℝ≥0) : ℝ) = _ from
      NNReal.toRealHom.toMonoidHom.map_finprod (GlobalTheory.Doubling.finite_mulSupport_absEv l)]
    refine finprod_congr fun v => ?_
    rw [GlobalTheory.Doubling.absEv_unitFin]
    rfl

theorem ext_map (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding)
    (b : InfiniteAdeleRing F) :
    InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) b W) =
      InfinitePlace.Completion.extensionEmbedding w (b w) := by
  refine congrFun ((InfiniteAdeleRing.denseRange_algebraMap F).equalizer
    ((InfinitePlace.Completion.isometry_extensionEmbedding W).continuous.comp ((continuous_apply W).comp
      (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap (K := F) (L := E))))
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)) (funext fun k => ?_)) b
  change InfinitePlace.Completion.extensionEmbedding W (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E)
    (algebraMap F (InfiniteAdeleRing F) k) W) = _
  rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
  simpa only [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.algebraMap_def,
    WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, RingEquiv.apply_symm_apply,
    Function.comp_apply, WithAbs.equiv] using (InfinitePlace.Completion.extensionEmbedding_coe W (WithAbs.toAbs W.1 (algebraMap F E k))).trans
    ((RingHom.congr_fun h k).trans (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs w.1 k)).symm)

theorem ext_Φ (W : InfinitePlace E) {w : InfinitePlace F} (h : W.embedding.comp (algebraMap F E) = w.embedding) (l : AE F E) :
    InfinitePlace.Completion.extensionEmbedding W ((Φ F E l).1 W) = piInf (⟨W.embedding, h⟩ : EmbOver E w) l := by
  induction l using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact map_zero _
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), ← hx, ← hy]; exact map_add _ _ _
  | tmul a x =>
    rw [adeleTensorAlgEquivLeft_tmul]
    change InfinitePlace.Completion.extensionEmbedding W ((algebraMap E (AdeleRing (𝓞 E) E) x).1 W *
      GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (L := E) a.1 W) =
      InfinitePlace.Completion.extensionEmbedding w (a.1 w) * W.embedding x
    rw [map_mul, ext_map W h, mul_comm]
    simpa only [AdeleRing.algebraMap_fst_apply, AbsoluteValue.Completion.algebraMap_def,
      WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.equiv_apply, WithAbs.ofAbs_toAbs] using
      congrArg _ (InfinitePlace.Completion.extensionEmbedding_coe W (WithAbs.toAbs W.1 x))

theorem norm_le (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : InfinitePlace E) (l : (AE F E)ˣ) :
    ‖(Φ F E l).1 W‖ ≤ ∑ w, ‖piInf (τ w) (l : AE F E)‖ := by
  haveI := h.1
  let w := InfinitePlace.mk (W.embedding.comp (algebraMap F E))
  have hw : W.embedding.comp (algebraMap F E) = w.embedding :=
    (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal w))).symm
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding W).norm_map_of_map_zero (map_zero _), ext_Φ W hw]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun w => ‖piInf (τ w) (l : AE F E)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ w))
  have := (GlobalTheory.Doubling.absEw_eq_sq h (⟨W.embedding, hw⟩ : EmbOver E w) (GlobalTheory.Doubling.unitInf F E w l)).symm.trans
    (GlobalTheory.Doubling.absEw_eq_sq h (τ w) (GlobalTheory.Doubling.unitInf F E w l))
  exact congrArg NNReal.toReal ((pow_left_inj₀ zero_le' zero_le' two_ne_zero).1 this)

theorem snd_eq {l c : AE F E} (h : At (evI F) (l - c)) : (Φ F E l).2 = (Φ F E c).2 := by
  let u : AF F := ((0 : Ainf F), (1 : Af F))
  have h0 := congrArg (Φ F E) (h u (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)))
  rw [map_smul, map_zero, map_sub, Algebra.smul_def] at h0
  have h1 := congrArg Prod.snd h0
  change finiteAdeleMap F E 1 * ((Φ F E l).2 - (Φ F E c).2) = 0 at h1
  rwa [map_one, one_mul, sub_eq_zero] at h1

end Tate

theorem tateAbs : TateAbs := by
  intro F E _ _ _ _ _ σ B hB μ hμ z hz
  classical
  obtain ⟨-, _, _, _, _, _, -⟩ := ideleTop F E
  have hz1 : (1 : ℝ) < z := by exact_mod_cast hz
  have hk : 2 * (z : ℝ) + 2 < (2 * z + 3 : ℕ) := by push_cast; linarith
  refine ⟨(2 * z + 3) * Fintype.card (InfinitePlace E), fun C hC => ?_⟩
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hC.image (continuous_snd.comp (Tate.cont_Φ (F := F) (E := E))))
  refine lt_of_le_of_lt ?_ (Tate.transport (Tate.Ψ F E) μ hz1 hk L)
  have hT : IsOpen {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L} :=
    (isOpen_idealFiniteAdeles L).preimage (continuous_snd.comp (Tate.cont_Φ.comp Units.continuous_val))
  refine le_trans (lintegral_mono_set (t := {l : (AE F E)ˣ | (Tate.Φ F E l).2 ∈ idealFiniteAdeles L})
    fun l ⟨c, hc, hl⟩ => hL ⟨c, hc, (Tate.snd_eq hl).symm⟩) ?_
  refine le_trans (setLIntegral_mono' hT.measurableSet fun l hl => ENNReal.ofReal_le_ofReal ?_) (setLIntegral_le_lintegral _ _)
  have hm : (IdeleGroup.toFinite E (Tate.Ψ F E l) : FiniteAdeleRing (𝓞 E) E) ∈ idealFiniteAdeles L := hl
  rw [finiteZetaBound, if_pos hm, Tate.absE_eq, ← Real.rpow_natCast, ideleModule_rpow_eq, infiniteZetaBound,
    Finset.prod_div_distrib, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_left (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
    (Real.rpow_nonneg (IdeleGroup.finiteModule_pos _).le _)) (Finset.prod_pos fun _ _ => by positivity) ?_
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun W _ => pow_le_pow_left₀ (by positivity) ?_ _
  exact add_le_add le_rfl (Tate.norm_le hB.cm B.emb W l)

end PositivityTheory.ThKCT

end
end
