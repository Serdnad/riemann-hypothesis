module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleLocalSectionsGlueBasicOpenCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

noncomputable section
namespace GlobalTheory.StabHaar
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_mul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g * mat g⁻¹ = 1 := by
  show (g.1 * g.1⁻¹ : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_inv_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 := by
  show (g.1⁻¹ * g.1 : GL (Fin n) (AE F E)).1 = 1
  simp

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

def stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : Subgroup (UA σ X.J) where
  carrier := {g | (∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)) ∧
    ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X}
  one_mem' := by
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]; exact Commute.one_left _
    · simp only [inv_one, mat_one, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · rw [mat_mul, Matrix.map_mul]; exact (hg1 w).mul_left (hh1 w)
    · rw [mul_inv_rev, mat_mul, mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact ⟨(hg2 _ (hh2 z hz).1).1, (hh2 _ (hg2 z hz).2).2⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun w => ?_, fun z hz => ?_⟩
    · set A := (mat g).map (piInf (B.emb w))
      set A' := (mat g⁻¹).map (piInf (B.emb w))
      have e1 : A * A' = 1 := by
        rw [← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
      have e2 : A' * A = 1 := by
        rw [← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      have hc := hg1 w
      show A' * X.θ w = X.θ w * A'
      calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [e1, Matrix.mul_one]
        _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
        _ = A' * (A * X.θ w) * A' := by rw [hc.eq]
        _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
        _ = X.θ w * A' := by rw [e2, Matrix.one_mul]
    · rw [inv_inv]; exact ⟨(hg2 z hz).2, (hg2 z hz).1⟩

theorem isStab_stabK (B : Base F E) {n : ℕ} (X : Spc F E n) : IsStab B (stabK (σ := σ) B X) := fun _ => Iff.rfl

theorem exists_haar_of_isCompact {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (K : Subgroup (UA σ J))
    (hK : IsCompact (K : Set (UA σ J))) : ∃ μ : Measure K, μ.IsHaarMeasure := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _⟩

theorem exists_haar_idele : ∃ μ : Measure (AE F E)ˣ, μ.IsHaarMeasure := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (AE F E)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem isClosed_stabK (B : Base F E) {n : ℕ} (X : Spc F E n)
    (hL : IsClosed ((latHat X : AddSubgroup (Fin n → AE F E)) : Set (Fin n → AE F E))) :
    IsClosed ((stabK (σ := σ) B X : Subgroup (UA σ X.J)) : Set (UA σ X.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hm : Continuous fun g : UA σ X.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hmi : Continuous fun g : UA σ X.J => mat g⁻¹ := hm.comp continuous_inv
  have hp : ∀ w, Continuous (piInf (B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (B.emb w)
  have h1 : IsClosed {g : UA σ X.J | ∀ w, Commute ((mat g).map (piInf (B.emb w))) (X.θ w)} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun w => isClosed_eq ((hm.matrix_map (hp w)).matrix_mul continuous_const)
      (continuous_const.matrix_mul (hm.matrix_map (hp w)))
  have h2 : IsClosed {g : UA σ X.J | ∀ z ∈ latHat X, mat g *ᵥ z ∈ latHat X ∧ mat g⁻¹ *ᵥ z ∈ latHat X} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun z => isClosed_iInter fun _ => ?_
    exact (hL.preimage (hm.matrix_mulVec continuous_const)).inter (hL.preimage (hmi.matrix_mulVec continuous_const))
  exact h1.inter h2

end GlobalTheory.StabHaar
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaIntegralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_smul (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) :
    M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : Rep σ Y W) (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) : M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← integral_add (hconv Φ hΦ h) (hconv Ψ hΨ h)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add (f := _), thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΨ)]

theorem snd_eq_zero_of_at {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz u hu) i)
  rwa [one_mul] at h1

end GlobalTheory.ThetaIntegralLine
end
end

section

noncomputable section

namespace GlobalTheory.ThKConst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  obtain ⟨c₁, t₁⟩ := h₁
  obtain ⟨c₂, t₂⟩ := h₂
  have e : ⇑(χ₁ / χ₂) = fun x => χ₁ x / χ₂ x := funext fun x => MonoidHom.div_apply χ₁ χ₂ x
  exact And.intro (by rw [e]; exact c₁.div' c₂) fun x => by rw [MonoidHom.div_apply, t₁ x, t₂ x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂]
  split_ifs
  · norm_num
  · rcases Nat.even_or_odd n₁ with h | h
    · rw [h.neg_one_pow, ((Nat.even_add.mp he).mp h).neg_one_pow, hn.neg_one_pow]
      norm_num
    · have h' : Odd n₂ := Nat.not_even_iff_odd.mp fun h'' => (Nat.not_even_iff_odd.mpr h) ((Nat.even_add.mp he).mpr h'')
      rw [h.neg_one_pow, h'.neg_one_pow, hn.neg_one_pow]
      norm_num

variable {a a' : ℕ}

theorem isPair_small {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_div h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_div h.chars.resα h.chars.resβ (Nat.even_add.mpr (Nat.even_add.mp h.geo.even).symm) h.geo.even
    weil := h.weil' }

theorem thetaSum_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ?_) ?_
  · simp [thetaSum]
  · intro k s hk ih hf
    have hs : ∀ j ∈ s, f j ∈ schA F κ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      thetaSum_add F (hf k (Finset.mem_insert_self k s)) (Submodule.sum_mem _ hs), ih hs]

end GlobalTheory.ThKConst
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.isFreeGenerator_topForms_of_formallyUnramified : ∀ {k A B : Type} [CommRing k] [CommRing A] [CommRing B] (α : k →+* A) (β : k →+* B) (ψ : A →+* B) (h : ψ.comp α = β) (n : ℕ), (letI := ψ.toAlgebra; Algebra.FormallyUnramified A B) → ∀ ω : Forms α n, IsFreeGen A ω → (∃ ω' : Forms β n, IsFreeGen B ω') → IsFreeGen B (TopForm.formMap n ψ h ω) := by
  first | exact @GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | exact GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified | (intros; apply GlobalTheory.TopForm.isFreeGen_formMap_of_formallyUnramified <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PtExt.CocSec

variable {R : Type} [CommRing R]

def liftU {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D) (ψ : D →ₐ[R] E)
    (h : IsUnit (ψ t)) : Localization.Away t →ₐ[R] E :=
  IsLocalization.liftAlgHom (M := Submonoid.powers t) (f := ψ) (by
    rintro ⟨_, m, rfl⟩
    simpa using h.pow m)

theorem liftU_comp {D E : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] (t : D)
    (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) :
    (liftU t ψ h).comp (IsScalarTower.toAlgHom R D (Localization.Away t)) = ψ := by
  ext r
  simp [liftU]

theorem comp_liftU {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E']
    [Algebra R E'] (t : D) (ψ : D →ₐ[R] E) (h : IsUnit (ψ t)) (θ : E →ₐ[R] E') :
    θ.comp (liftU t ψ h) = liftU t (θ.comp ψ) (h.map θ) := by
  apply IsLocalization.algHom_ext (Submonoid.powers t)
  ext r
  have h1 := DFunLike.congr_fun (liftU_comp t ψ h) r
  have h2 := DFunLike.congr_fun (liftU_comp t (θ.comp ψ) (h.map θ)) r
  simp only [AlgHom.comp_apply] at h1 h2 ⊢
  exact (congrArg θ h1).trans h2.symm

end GlobalTheory.PtExt.CocSec

end


open GlobalTheory.PtExt.CocSec in
theorem GlobalTheory.PtExt.CocSec.exists_section :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc W u →
      ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
      ∃ σ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E,
        ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
          (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'),
          Sm W (D := E) (spOver ψ ≫ x) →
            σ E' (θ.comp ψ) - θ (σ E ψ) = u E E' θ (spOver ψ ≫ x) := by
  intro R _ X K W hW u hu D _ _ x
  obtain ⟨n, s, hs, hsm⟩ := GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover R X K W hW D x
  classical
  let k : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E := fun a E _ _ ψ ↦
    if h : IsUnit (ψ (s a)) then
      u (Localization.Away (s a)) E (liftU (s a) ψ h)
        (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x)
    else 0
  have hk : ∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
      k a E' (θ.comp ψ) - θ (k a E ψ) = u E E' θ (spOver ψ ≫ x) := by
    intro a E _ _ E' _ _ ψ θ h
    have h' : IsUnit ((θ.comp ψ) (s a)) := h.map θ
    simp only [k, dif_pos h, dif_pos h']
    rw [← comp_liftU (s a) ψ h θ, hu _ _ _ (liftU (s a) ψ h) θ _ (hsm a), ← Category.assoc,
      spOver_comp, liftU_comp]
    ring
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.cech_first_cohomology_away_natural R D n s hs (fun a b E _ _ ψ ↦ k a E ψ - k b E ψ)
    (fun a b E _ _ E' _ _ ψ θ ha hb ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := hk b E E' ψ θ hb
      simp only [map_sub]
      linear_combination h1 - h2)
    (fun a b c E _ _ ψ _ _ _ ↦ by ring)
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.pointwiseCocycle_local_sections_glue_basicOpen_cover R X K W u hu D x n s hs (fun a E _ _ ψ ↦ k a E ψ + e a E ψ)
    (fun a E _ _ E' _ _ ψ θ ha ↦ by
      have h1 := hk a E E' ψ θ ha
      have h2 := he1 a E E' ψ θ ha
      simp only [map_add (f := _)]
      linear_combination h1 + h2)
    (fun a b E _ _ ψ ha hb ↦ by
      have h := he2 a b E ψ ha hb
      linear_combination h)
  exact ⟨σ, hσ⟩
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

open Algebra.TensorProduct in
theorem coc_mem_symCocycles (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (hg : IsSymCoc d.g) (n : ℕ) :
    d.coc n ∈ symCocycles R (G.A n) := by
  set H := G.A n

  have V : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      lift φ ψ (fun _ _ ↦ Commute.all _ _) (d.coc n) = d.g D (spOver φ ≫ t.y n) (spOver ψ ≫ t.y n) -
        ((fv d.f H D (toConv φ * toConv ψ).ofConv (t.y n) + (toConv φ * toConv ψ).ofConv (d.h n)) -
          (fv d.f H D φ (t.y n) + φ (d.h n)) - (fv d.f H D ψ (t.y n) + ψ (d.h n))) :=
    fun D _ _ φ ψ ↦ GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue R A p G t c d n D φ ψ
  have M : ∀ (D : Type) [CommRing D] [Algebra R D] (φ ψ : H →ₐ[R] D),
      spOver (toConv φ * toConv ψ).ofConv ≫ t.y n = (spOver φ ≫ t.y n) * (spOver ψ ≫ t.y n) :=
    fun D _ _ φ ψ ↦ t.mul n D (toConv φ) (toConv ψ)
  rw [mem_symCocycles]
  constructor
  · let i1 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := includeLeft
    let i2 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeLeft
    let i3 : H →ₐ[R] H ⊗[R] (H ⊗[R] H) := (includeRight : H ⊗[R] H →ₐ[R] H ⊗[R] (H ⊗[R] H)).comp includeRight
    let i12 := (toConv i1 * toConv i2).ofConv
    let i23 := (toConv i2 * toConv i3).ofConv
    have e1 : ∀ x : H ⊗[R] H, (1 : H) ⊗ₜ[R] x = lift i2 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [tmul_add, map_add (f := _), hx, hy]
      | tmul a b => simp [i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e2 : ∀ x : H ⊗[R] H, TensorProduct.assoc R H H H ((Coalgebra.comul (R := R) (A := H)).rTensor H x) =
        lift i12 i3 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, lift_tmul]
        simp only [i12, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) a : H ⊗[R] H) with
        | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy, add_mul]
        | tmul a1 a2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e3 : ∀ x : H ⊗[R] H, (Coalgebra.comul (R := R) (A := H)).lTensor H x = lift i1 i23 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b =>
        rw [LinearMap.lTensor_tmul, lift_tmul]
        simp only [i23, AlgHom.convMul_apply]
        induction (Coalgebra.comul (R := R) b : H ⊗[R] H) with
        | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy, mul_add]
        | tmul b1 b2 => simp [i1, i2, i3, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e4 : ∀ x : H ⊗[R] H, ((TensorProduct.mk R H H).flip 1).lTensor H x =
        lift i1 i2 (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [i1, i2, Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    rw [cobTwo_apply, e1, e2, e3, e4, V, V, V, V]
    simp only [i12, i23, toConv_ofConv, M]
    rw [_root_.mul_assoc (toConv i1) (toConv i2) (toConv i3)]
    have hc := (hg (H ⊗[R] (H ⊗[R] H))).2 (spOver i1 ≫ t.y n) (spOver i2 ≫ t.y n) (spOver i3 ≫ t.y n)
    linear_combination hc
  · have e : ∀ x : H ⊗[R] H, TensorProduct.comm R H H x =
        lift (includeRight : H →ₐ[R] H ⊗[R] H) (includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ ↦ Commute.all _ _) x := by
      intro x
      induction x with
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul, includeLeft_apply, includeRight_apply]
    have e' : d.coc n = lift (includeLeft : H →ₐ[R] H ⊗[R] H) includeRight (fun _ _ ↦ Commute.all _ _) (d.coc n) := by
      exact (DFunLike.congr_fun (lift_includeLeft_includeRight (R := R) (S := R) (A := H) (B := H)) (d.coc n)).symm
    rw [e, V]
    conv_rhs => rw [e', V]
    rw [mul_comm (toConv (includeRight : H →ₐ[R] H ⊗[R] H)), (hg _).1]
    ring

end GlobalTheory.PtExt
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.canonicalRigidifiedExtensionOfDeRhamClass_unique
    (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (hA : IsAbelianScheme A) (x x' : G.RigExt)
    (hx : IsCan t c x) (hx' : IsCan t c x') : x = x' :=
  GlobalTheory.PtExt.isCan_unique R A p G t c hA x x' hx hx'
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  first | exact @GlobalTheory.PtExt.isSymCoc_of_isAdd | exact GlobalTheory.PtExt.isSymCoc_of_isAdd | (intros; apply GlobalTheory.PtExt.isSymCoc_of_isAdd <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tangentPullback_primitiveCrystallineClass_epsPart_isCob : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (f : Z1 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))), CatCoh.H1.mk _ f ∈ primDR (A ⊗ B) → ∀ v : epsR R ⟶ B, Cohom (whole A) (sndPull (fv f) v) (Fn1.zero A) := by
  first | exact @GlobalTheory.PtExt.cohom_sndPull_zero | exact GlobalTheory.PtExt.cohom_sndPull_zero | (intros; apply GlobalTheory.PtExt.cohom_sndPull_zero <;> assumption)
end
