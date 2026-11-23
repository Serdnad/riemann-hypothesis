module

public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.AutomorphicForms.CuspidalAdmissible
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import GroundTheory.AutomorphicForms.RealIwasawaSubgroups
public import GroundTheory.AutomorphicForms.RealIwasawaIntegration
public import GroundTheory.AutomorphicForms.ReductionLocalVolumeGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem fixedVectors_jacquetRep_congruenceSubgroup (m : ℕ) :
    fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) =
      fixedVectors (jacquetAction F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  ext x
  simp only [mem_fixedVectors]
  refine forall₂_congr fun y hy => ?_
  rw [jacquetRep, twist_apply, MonoidHom.comp_apply,
    invSqrtModular_leviIncl_of_mem y (congruenceSubgroup_le F n m (Subgroup.mem_subgroupOf.1 hy)),
    one_smul]

theorem isAdmissible_jacquetRep (hπ : IsAdmissible π) : IsAdmissible (jacquetRep F n β π) := by
  refine ⟨isSmooth_jacquetRep π hπ.1, fun L hLc hLo => ?_⟩
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hLo.mem_nhds L.one_mem)
  set m := max m₁ 1
  have hle : (congruenceSubgroup F n m).subgroupOf (levi F n β) ≤ L := fun x hx =>
    hm₁ (Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (le_max_left _ _)
      (Subgroup.mem_subgroupOf.1 hx)))
  have : FiniteDimensional ℂ (fixedVectors π (congruenceSubgroup F n m)) :=
    hπ.2 _ (isCompact_congruenceSubgroup F n m) (isOpen_congruenceSubgroup F n m)
  have hfin : FiniteDimensional ℂ
      (fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β))) := by
    rw [fixedVectors_jacquetRep_congruenceSubgroup]
    exact Module.Finite.of_surjective _
      (jacquetFixedMap_surjective_congruenceSubgroup β hπ (le_max_right m₁ 1))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)

end Parabolic

end GroundTheory.Automorphic
end
end

section

open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

theorem eq_one_of_isCompact {G : Type*} [Group G] [TopologicalSpace G] {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (f : G →* {r : ℝ // 0 < r}) (hf : Continuous fun g => (f g : ℝ))
    {h : G} (hh : h ∈ H) : f h = 1 := by
  obtain ⟨M, hM⟩ := hH.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ m : ℕ, (f h : ℝ) ^ m ≤ M ∧ ((f h : ℝ)⁻¹) ^ m ≤ M := fun m => by
    have h1 := hM (h ^ m) (pow_mem hh m)
    have h2 := hM ((h⁻¹) ^ m) (pow_mem (inv_mem hh) m)
    rw [map_pow, Positive.val_pow, Real.norm_eq_abs, abs_of_pos (pow_pos (f h).2 m)] at h1
    rw [map_pow, map_inv, Positive.val_pow, Positive.coe_inv, Real.norm_eq_abs,
      abs_of_pos (pow_pos (inv_pos.2 (f h).2) m)] at h2
    exact ⟨h1, h2⟩
  refine Subtype.ext ?_
  rw [Positive.val_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 < (f h : ℝ)⁻¹ := (one_lt_inv₀ (f h).2).2 hlt
    obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).2 (not_le.2 hm)
  · obtain ⟨m, hm⟩ := (tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop M |>.exists
    exact absurd (hbound m).1 (not_le.2 hm)

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def normDet (w : InfinitePlace K) : GL (Fin n) w.Completion →* {r : ℝ // 0 < r} where
  toFun g := ⟨‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖, norm_pos_iff.2 (by
    have := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
    exact this.ne_zero)⟩
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.det_mul]

theorem continuous_normDet (w : InfinitePlace K) :
    Continuous fun g : GL (Fin n) w.Completion => (normDet (n := n) w g : ℝ) :=
  (Continuous.matrix_det (Units.continuous_val (M := Matrix (Fin n) (Fin n) w.Completion))).norm

theorem norm_det_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) : ‖(k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 := by
  have := eq_one_of_isCompact (isCompact_archCompact w) (normDet w) (continuous_normDet w) hk
  exact congrArg Subtype.val this

theorem norm_det_infAt_of_mem_maxCompact {k : AdelicGLn.AdelicGL K n} (hk : k ∈ maxCompact)
    (w : InfinitePlace K) : ‖(infAt w k : Matrix (Fin n) (Fin n) w.Completion).det‖ = 1 :=
  norm_det_of_mem_archCompact (hk.1 w)

theorem infAt_diagUnits (w : InfinitePlace K) (f : Fin n → IdeleGroup K) :
    infAt w (diagUnits n f) = diagUnits n (fun i => infiniteProj w (f i)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [infAt_apply, coe_diagUnits, coe_diagUnits, diagonal_apply, diagonal_apply]
  split_ifs
  · rw [coe_infiniteProj]
  · rfl

theorem infAt_diagUnits_posIdele (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    infAt w (diagUnits n fun i => posIdele (K := K) (r i) (hr i)) =
      diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) := by
  rw [infAt_diagUnits]
  congr 1
  funext i
  exact infiniteProj_posIdele (r i) (hr i) w

theorem norm_posRealToUnits (w : InfinitePlace K) {r : ℝ} (hr : 0 < r) :
    ‖((posRealToUnits w ⟨r ^ w.mult, pow_pos hr _⟩ : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have h := norm_posRealElem_pow w (pow_pos hr w.mult).le
  have hm : w.mult ≠ 0 := InfinitePlace.mult_ne_zero
  exact (pow_left_inj₀ (norm_nonneg _) hr.le hm).1 h

theorem norm_det_diagUnits_posRealToUnits (w : InfinitePlace K) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    ‖((diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) :
      GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).det‖ = ∏ i, r i := by
  rw [coe_diagUnits, det_diagonal, norm_prod]
  exact Finset.prod_congr rfl fun i _ => norm_posRealToUnits w (hr i)

theorem prodEquiv_diagUnits_posIdele_snd (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (AdelicGLn.prodEquiv K n (diagUnits n fun i => posIdele (K := K) (r i) (hr i))).2 = 1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [AdelicGLn.prodEquiv_apply_snd, coe_diagUnits, diagonal_apply]
  split_ifs with h
  · subst h
    refine RestrictedProduct.ext _ _ fun v => ?_
    have := posIdele_finite (K := K) (r a) (hr a) v
    exact this.trans (by simp; rfl)
  · rw [Units.val_one, Matrix.one_apply_ne h]
    rfl

end Reduction

end

end GroundTheory.Automorphic
end

section

open MeasureTheory Measure Set Matrix NumberField
open scoped NNReal ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem mem_unitaryGroup_of_euclidNorm {M : Matrix (Fin n) (Fin n) 𝕜}
    (hM : ∀ y : Fin n → 𝕜, euclidNorm (y ᵥ* M) = euclidNorm y) : M ∈ unitaryGroup (Fin n) 𝕜 := by
  classical
  let L : EuclideanSpace 𝕜 (Fin n) →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
    { toFun := fun x => WithLp.toLp 2 (WithLp.ofLp x ᵥ* M)
      map_add' := fun x y => by simp [add_vecMul]
      map_smul' := fun c x => by simp [smul_vecMul]
      norm_map' := fun x => by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        exact hM (WithLp.ofLp x) }
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := L.inner_map_map (WithLp.toLp 2 (Pi.single j (1 : 𝕜))) (WithLp.toLp 2 (Pi.single i (1 : 𝕜)))
  simp only [L, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    EuclideanSpace.inner_toLp_toLp, single_one_vecMul] at h
  rw [Matrix.mul_apply]
  change (∑ k, M i k * star M k j) = if i = j then 1 else 0
  have h2 : ∑ k, M i k * star M k j = M.row i ⬝ᵥ star (M.row j) := by
    simp [dotProduct, Matrix.row, Matrix.star_apply]
  rw [h2, h, single_one_dotProduct, Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

end Unitary

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {m : ℕ}
  [MeasurableSpace (GL (Fin (m + 1)) E)] [BorelSpace (GL (Fin (m + 1)) E)]
  [MeasurableSpace (GL (Fin (m + 1)) 𝕜)] [BorelSpace (GL (Fin (m + 1)) 𝕜)]

theorem measure_lt_top_of_ringEquiv (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    [MeasurableSpace (unitaryGroup (Fin (m + 1)) 𝕜)] [BorelSpace (unitaryGroup (Fin (m + 1)) 𝕜)]
    (hANK : ∀ (ν : Measure (GL (Fin (m + 1)) 𝕜)) [ν.IsHaarMeasure]
      (μK : Measure (unitaryGroup (Fin (m + 1)) 𝕜)) [μK.IsHaarMeasure]
      (μA : Measure (diagPosSubgroup (Fin (m + 1)) 𝕜)) [μA.IsHaarMeasure]
      (μN : Measure (upperUnipotentSubgroup (Fin (m + 1)) 𝕜)) [μN.IsHaarMeasure],
      ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ f : GL (Fin (m + 1)) 𝕜 → ℝ≥0∞, Measurable f →
        ∫⁻ g, f g ∂ν = c * ∫⁻ a, ∫⁻ u, ∫⁻ k, f (a * u * Unitary.toUnits k) ∂μK ∂μN ∂μA)
    (μ : Measure (GL (Fin (m + 1)) E)) [μ.IsHaarMeasure]
    (D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) E)
    (hD : ∀ r, ((D r : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
      diagonal fun i => ((r.1 i : ℝ) : 𝕜))
    {ω : Set (GL (Fin (m + 1)) E)} (hω : IsCompact ω)
    (hωB : ∀ b ∈ ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) E).IsUpperTriangular)
    {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁) :
    μ {g | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ ∧
      ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ ≤ c₂ ∧
      ∃ b ∈ ω, ∃ r : PosDiag (Fin (m + 1)), (∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc) ∧
        ∃ k : GL (Fin (m + 1)) E, (∀ y : Fin (m + 1) → E,
          euclidNorm (y ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) = euclidNorm y) ∧
          g = b * D r * k} < ⊤ := by
  classical
  have hφc : Continuous φ := (AddMonoidHomClass.isometry_of_norm φ hφ).continuous
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  have hφc' : Continuous φ.symm := (AddMonoidHomClass.isometry_of_norm φ.symm hφ').continuous
  set e : Matrix (Fin (m + 1)) (Fin (m + 1)) E ≃* Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜 :=
    φ.mapMatrix.toMulEquiv with he
  set Φ : GL (Fin (m + 1)) E ≃ₜ* GL (Fin (m + 1)) 𝕜 :=
    unitsCongr e (continuous_id.matrix_map hφc) (continuous_id.matrix_map hφc') with hΦ
  have hΦv : ∀ g : GL (Fin (m + 1)) E,
      ((Φ g : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) =
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ := fun g => rfl
  set ν : Measure (GL (Fin (m + 1)) 𝕜) := Measure.map Φ μ with hν
  have hνH : ν.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hω' : IsCompact (Φ '' ω) := hω.image Φ.continuous
  have hωB' : ∀ b ∈ Φ '' ω, (b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).IsUpperTriangular := by
    rintro _ ⟨b, hb, rfl⟩ i j hij
    rw [hΦv, Matrix.map_apply, hωB b hb hij, map_zero]
  have hfin := measure_siegelGL_lt_top (c₂ := c₂) ν (fun μK _ μA _ μN _ => hANK ν μK μA μN) hω' hωB'
    ht hc₁
  have hmeas : MeasurableSet (siegelGL (Φ '' ω) t c₁ c₂) := (isClosed_siegelGL hω' t c₁ c₂).measurableSet
  refine lt_of_le_of_lt (measure_mono ?_) ((Measure.map_apply Φ.continuous.measurable hmeas).symm ▸
    hfin)
  rintro g ⟨hd1, hd2, b, hbω, r, hr, k, hk, rfl⟩
  change Φ (b * D r * k) ∈ siegelGL (Φ '' ω) t c₁ c₂
  have hdet : ‖((Φ (b * D r * k) : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜).det‖ =
      ‖((b * D r * k : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).det‖ := by
    rw [hΦv]
    have h1 := RingHom.map_det (φ : E →+* 𝕜) ((b * D r * k : GL (Fin (m + 1)) E) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) E)
    rw [RingHom.mapMatrix_apply] at h1
    change ‖(((b * D r * k : GL (Fin (m + 1)) E) : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map
      (φ : E →+* 𝕜)).det‖ = _
    rw [← h1]
    exact hφ _
  have hkU : ((Φ k : GL (Fin (m + 1)) 𝕜) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝕜) ∈
      unitaryGroup (Fin (m + 1)) 𝕜 := by
    refine mem_unitaryGroup_of_euclidNorm fun y => ?_
    have hy : y = fun i => φ (φ.symm (y i)) := by funext i; simp
    rw [hy, hΦv]
    have : (fun i => φ (φ.symm (y i))) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E).map φ =
        fun j => φ.toRingHom (((fun i => φ.symm (y i)) ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) E)) j) := by
      ext j

      simp [vecMul, dotProduct, _root_.map_sum, map_mul]
    rw [this, euclidNorm_map φ.toRingHom hφ, hk, ← euclidNorm_map φ.toRingHom hφ]
    rfl
  refine ⟨hd1.trans_eq hdet.symm, hdet.trans_le hd2, Φ b, ⟨b, hbω, rfl⟩, r, hr,
    ⟨_, hkU⟩, ?_⟩
  rw [map_mul, map_mul]
  congr 1
  · congr 1
    apply Units.ext
    rw [hΦv, hD, coe_diagPosOf]
  · apply Units.ext
    rfl

end Transport

section Place

open GroundTheory.Global

variable {K : Type*} [Field K]

def localSiegel (w : InfinitePlace K) {n : ℕ} (ω : Set (GL (Fin n) w.Completion)) (t c₁ c₂ : ℝ) :
    Set (GL (Fin n) w.Completion) :=
  {g | c₁ ≤ ‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖ ∧
    ‖(g : Matrix (Fin n) (Fin n) w.Completion).det‖ ≤ c₂ ∧
    ∃ b ∈ ω, ∃ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) ∧
      ∃ k ∈ archCompact w,
        g = b * diagUnits n (fun i => posRealToUnits w ⟨r i ^ w.mult, pow_pos (hr i) _⟩) * k}

theorem measure_localSiegel_lt_top (w : InfinitePlace K) {n : ℕ}
    [MeasurableSpace (GL (Fin n) w.Completion)] [BorelSpace (GL (Fin n) w.Completion)]
    (μ : Measure (GL (Fin n) w.Completion)) [μ.IsHaarMeasure] {ω : Set (GL (Fin n) w.Completion)}
    (hω : IsCompact ω) (hωB : ∀ b ∈ ω, (b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular)
    {t c₁ c₂ : ℝ} (ht : 0 < t) (hc₁ : 0 < c₁) : μ (localSiegel w ω t c₁ c₂) < ⊤ := by
  classical
  cases n with
  | zero =>
    have hs : (Set.univ : Set (GL (Fin 0) w.Completion)).Subsingleton := fun x _ y _ =>
      Units.ext (Subsingleton.elim _ _)
    exact lt_of_le_of_lt (measure_mono (subset_univ _)) hs.isCompact.measure_lt_top
  | succ m =>
    set D : PosDiag (Fin (m + 1)) → GL (Fin (m + 1)) w.Completion := fun r =>
      diagUnits (m + 1) (fun i => posRealToUnits w ⟨r.1 i ^ w.mult, pow_pos (r.2 i) _⟩) with hDdef
    have hsub : localSiegel w ω t c₁ c₂ ⊆
        {g | c₁ ≤ ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).det‖ ∧
          ‖(g : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion).det‖ ≤ c₂ ∧
          ∃ b ∈ ω, ∃ r : PosDiag (Fin (m + 1)), (∀ l : Fin m, t * r.1 l.succ ≤ r.1 l.castSucc) ∧
            ∃ k : GL (Fin (m + 1)) w.Completion, (∀ y : Fin (m + 1) → w.Completion,
              euclidNorm (y ᵥ* (k : Matrix (Fin (m + 1)) (Fin (m + 1)) w.Completion)) = euclidNorm y) ∧
              g = b * D r * k} := by
      rintro g ⟨h1, h2, b, hb, r, hr, hrat, k, hk, rfl⟩
      exact ⟨h1, h2, b, hb, ⟨r, hr⟩, fun l => hrat l.castSucc l.succ (by simp), k, hk, rfl⟩
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    by_cases hw : w.IsReal
    · have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x =>
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) x
      refine measure_lt_top_of_ringEquiv (𝕜 := ℝ)
        (InfinitePlace.Completion.ringEquivRealOfIsReal hw) hφ
        (fun ν _ μK _ μA _ μN _ => lintegral_GLReal_ANK ν μK μA μN) μ D (fun r => ?_) hω hωB ht hc₁
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      have hm : w.mult = 1 := by simp [InfinitePlace.mult, hw]
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_pos hw, RingEquiv.apply_symm_apply, hm, pow_one]
      rfl
    · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
      have hφ : ∀ x, ‖InfinitePlace.Completion.ringEquivComplexOfIsComplex hc x‖ = ‖x‖ := fun x =>
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
      refine measure_lt_top_of_ringEquiv (𝕜 := ℂ)
        (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) hφ
        (fun ν _ μK _ μA _ μN _ => lintegral_GLComplex_ANK ν μK μA μN) μ D (fun r => ?_) hω hωB ht hc₁
      rw [hDdef]
      dsimp only
      rw [coe_diagUnits, diagonal_map (map_zero _)]
      congr 1
      funext i
      have hm : w.mult = 2 := by simp [InfinitePlace.mult, hw]
      simp only [posRealToUnits, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, posRealElem,
        dif_neg hw, RingEquiv.apply_symm_apply, hm]
      rw [Real.sqrt_sq (r.2 i).le]
      rfl

end Place

end Reduction

end

end GroundTheory.Automorphic
end
