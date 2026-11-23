module

public import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.GlobalFields.Adele.Bundle003
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle002
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Set Matrix
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Orbit

variable {𝒢 W : Type*} [Group 𝒢]

theorem exists_finset_of_orbit (Φ : 𝒢 → W) (G Γ : Subgroup 𝒢)
    (hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ G) (C : Set 𝒢)
    (hfin : (Φ '' C ∩ Φ '' (Γ : Set 𝒢)).Finite) :
    ∃ T : Finset 𝒢, (∀ δ ∈ T, δ ∈ Γ) ∧ ∀ g ∈ G, ∀ γ ∈ Γ, ∀ c ∈ C, g = γ * c →
      ∃ δ ∈ T, γ * δ ∈ G ∧ δ⁻¹ * c ∈ G := by
  classical
  have hch : ∀ s ∈ hfin.toFinset, ∃ δ ∈ Γ, Φ δ = s := fun s hs => by
    obtain ⟨-, δ, hδ, rfl⟩ := hfin.mem_toFinset.1 hs
    exact ⟨δ, hδ, rfl⟩
  choose! f hfΓ hfΦ using hch
  refine ⟨hfin.toFinset.image f, fun δ hδ => ?_, fun g hg γ hγ c hc hgc => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hδ
    exact hfΓ s hs
  · have h1 : Φ γ⁻¹ = Φ c := (hΦ _ _).2 (by rw [inv_inv, ← hgc]; exact hg)
    have hs : Φ c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨⟨c, hc, rfl⟩, γ⁻¹, inv_mem hγ, h1⟩
    refine ⟨f (Φ c), Finset.mem_image_of_mem _ hs, ?_, (hΦ _ _).1 (hfΦ _ hs)⟩
    have := (hΦ γ⁻¹ (f (Φ c))).1 (by rw [hfΦ _ hs, h1])
    rwa [inv_inv] at this

theorem conj_eq_conj_iff {R : Type*} [Ring R] (g g' : Rˣ) (x : R) :
    (g : R) * x * ↑g⁻¹ = g' * x * ↑g'⁻¹ ↔ ((g⁻¹ * g' : Rˣ) : R) * x = x * ((g⁻¹ * g' : Rˣ) : R) := by
  rw [Units.val_mul]
  have e1 : (↑g⁻¹ * ↑g' * x : R) = ↑g⁻¹ * (↑g' * x * ↑g'⁻¹) * ↑g' := by
    simp [mul_assoc]
  have e2 : (x * (↑g⁻¹ * ↑g') : R) = ↑g⁻¹ * (↑g * x * ↑g⁻¹) * ↑g' := by
    simp [mul_assoc]
  constructor
  · intro h
    rw [e1, e2, h]
  · intro h
    have e3 : (↑g' * x * ↑g'⁻¹ : R) = ↑g * (↑g⁻¹ * ↑g' * x) * ↑g'⁻¹ := by
      simp [mul_assoc]
    have e4 : (↑g * x * ↑g⁻¹ : R) = ↑g * (x * (↑g⁻¹ * ↑g')) * ↑g'⁻¹ := by
      simp [mul_assoc]
    rw [e3, e4, h]

end Orbit

variable {K : Type*} [Field K] [NumberField K]

theorem finite_algebraMap_preimage {X : Set 𝔸[K]} (hX : IsCompact X) :
    (algebraMap K 𝔸[K] ⁻¹' X).Finite := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hc := GroundTheory.Global.isClosed_principalSubgroup K
  set P : Set 𝔸[K] := (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) with hP
  have hXP : IsCompact (X ∩ P) := hX.inter_right hc
  have hdP : DiscreteTopology P := hd
  have hdisc : DiscreteTopology (X ∩ P : Set 𝔸[K]) :=
    DiscreteTopology.of_subset hdP Set.inter_subset_right
  have hfin : (X ∩ P).Finite := hXP.finite ⟨hdisc⟩
  refine (hfin.preimage (AdeleRing.algebraMap_injective (𝓞 K) K).injOn).subset ?_
  intro k hk
  exact ⟨hk, k, rfl⟩

theorem finite_of_isCompact_coords {α Y J : Type*} [Finite J] [TopologicalSpace Y] {X : Set Y}
    (hX : IsCompact X) (ψ : α → Y) (π : J → Y → 𝔸[K]) (hπ : ∀ j, Continuous (π j))
    (φ : α → J → K) (hφ : Function.Injective φ)
    (hψ : ∀ a j, π j (ψ a) = algebraMap K 𝔸[K] (φ a j)) : {a | ψ a ∈ X}.Finite := by
  have h : (Set.univ.pi fun j => algebraMap K 𝔸[K] ⁻¹' (π j '' X)).Finite :=
    Set.Finite.pi fun j => finite_algebraMap_preimage (hX.image (hπ j))
  refine Set.Finite.of_finite_image (h.subset ?_) hφ.injOn
  rintro _ ⟨a, ha, rfl⟩ j -
  exact ⟨ψ a, ha, hψ a j⟩

variable {n : ℕ} {m : Type*}

def adelicCentralizer (L : m → Matrix (Fin n) (Fin n) K) : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {g | ∀ k, (g : Matrix (Fin n) (Fin n) 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
    (L k).map (algebraMap K 𝔸[K]) * g}
  one_mem' k := by simp
  mul_mem' {a b} ha hb k := by
    show ((a * b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * _ = _ * _
    rw [Units.val_mul, Matrix.mul_assoc, hb k, ← Matrix.mul_assoc, ha k, Matrix.mul_assoc]
  inv_mem' {a} ha k := by
    have h := ha k
    set M := (L k).map (algebraMap K 𝔸[K])
    show ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M =
      M * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
    calc ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M
        = ↑a⁻¹ * (M * ↑a) * ↑a⁻¹ := by simp [mul_assoc]
      _ = ↑a⁻¹ * (↑a * M) * ↑a⁻¹ := by rw [h]
      _ = M * ↑a⁻¹ := by simp

theorem diagonal_mem_adelicCentralizer_iff {L : m → Matrix (Fin n) (Fin n) K}
    {γ : GL (Fin n) K} :
    AdelicGLn.diagonal K n γ ∈ adelicCentralizer L ↔
      ∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ := by
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) K => M.map (algebraMap K 𝔸[K]) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 K) K)
  refine forall_congr' fun k => ?_
  show (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
      (L k).map (algebraMap K 𝔸[K]) * (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) ↔ _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact hinj.eq_iff

theorem exists_isCompact_centralizer_reduction [Finite m] (L : m → Matrix (Fin n) (Fin n) K)
    (G : Subgroup (AdelicGLn.AdelicGL K n)) (hG1 : G ≤ Reduction.normOneGL (K := K) (n := n))
    (hGL : G ≤ adelicCentralizer L) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G, ∀ x : Fin n → K, x ≠ 0 → ε ≤ Reduction.height g x) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ G, ∃ γ : GL (Fin n) K,
      (∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ) ∧
        (AdelicGLn.diagonal K n γ)⁻¹ * g ∈ C := by
  classical
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
  let Lm : m → Matrix (Fin n) (Fin n) 𝔸[K] := fun k => (L k).map (algebraMap K 𝔸[K])
  let Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k *
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L := by
    intro g g'
    rw [funext_iff]
    exact forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)
  have hΦc : Continuous Φ := continuous_pi fun k =>
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)
  let ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun r k => (r k).map (algebraMap K 𝔸[K])
  have hψfin : {r | ψ r ∈ Φ '' C}.Finite := by
    refine finite_of_isCompact_coords (hC.image hΦc) ψ
      (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2)
      (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2)
      (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)
    intro r r' h
    funext k i j
    exact congrFun h (k, i, j)
  have hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite := by
    refine (hψfin.image ψ).subset ?_
    rintro _ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩
    have e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k *
        ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      funext k
      simp only [ψ, Φ, Lm, ← map_inv]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e] at hC1 ⊢
    exact ⟨_, hC1, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n)
    hΦ C hfin
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro g hg
  obtain ⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩ := hC' g (hG1 hg) (hh g hg)
  obtain ⟨δ, hδT, hγδ, hδc⟩ := hT g (hGL hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm
  obtain ⟨δ₀, rfl⟩ := hTΓ δ hδT
  refine ⟨γ₀ * δ₀, ?_, ?_⟩
  · rw [← diagonal_mem_adelicCentralizer_iff, map_mul]
    exact hγδ
  · refine Set.mem_biUnion hδT ⟨c, hc, ?_⟩
    rw [map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end Anisotropic

end

end GroundTheory.Automorphic
end

section

open NumberField IsDedekindDomain Topology Filter Set Matrix MeasureTheory
open scoped NumberField.AdeleRing RestrictedProduct ENNReal
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

noncomputable section

namespace Reduction

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def rpowHom (e : ℝ) : {r : ℝ // 0 < r} →* {r : ℝ // 0 < r} where
  toFun s := ⟨s.1 ^ e, Real.rpow_pos_of_pos s.2 e⟩
  map_one' := Subtype.ext (Real.one_rpow e)
  map_mul' s t := Subtype.ext (Real.mul_rpow s.2.le t.2.le)

theorem continuous_rpowHom (e : ℝ) : Continuous (rpowHom e) :=
  (continuous_subtype_val.rpow_const fun s => Or.inl s.2.ne').subtype_mk _


variable (K) in
def posIdeleHom : {r : ℝ // 0 < r} →* IdeleGroup K where
  toFun s := posIdele s.1 s.2
  map_one' := by
    unfold posIdele
    refine Finset.prod_eq_one fun w _ => ?_
    convert map_one (moduleSection (K := K) w)
    exact one_pow _
  map_mul' s t := by
    unfold posIdele
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp only [Positive.val_mul, mul_pow])

theorem posIdeleHom_apply (s : {r : ℝ // 0 < r}) : posIdeleHom K s = posIdele s.1 s.2 := rfl

theorem continuous_posIdeleHom : Continuous (posIdeleHom K) :=
  continuous_posIdele_subtype


variable (K n) in
def scalarUnits : IdeleGroup K →* AdelicGLn.AdelicGL K n :=
  (diagUnits n).comp
    { toFun := fun u _ => u, map_one' := rfl, map_mul' := fun _ _ => rfl }

theorem scalarUnits_apply (u : IdeleGroup K) : scalarUnits K n u = diagUnits n fun _ => u := rfl

theorem continuous_scalarUnits : Continuous (scalarUnits K n) :=
  (continuous_diagUnits n).comp (continuous_pi fun _ => continuous_id)

theorem scalarUnits_mul_comm (u : IdeleGroup K) (g : AdelicGLn.AdelicGL K n) :
    scalarUnits K n u * g = g * scalarUnits K n u := by
  refine Units.ext ?_
  simp only [Units.val_mul, scalarUnits_apply, coe_diagUnits]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]


variable (K) in
def centralSection (n : ℕ) : {r : ℝ // 0 < r} →* AdelicGLn.AdelicGL K n :=
  (scalarUnits K n).comp ((posIdeleHom K).comp (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹))

theorem continuous_centralSection : Continuous (centralSection K n) :=
  continuous_scalarUnits.comp (continuous_posIdeleHom.comp (continuous_rpowHom _))

theorem centralSection_mul_comm (s : {r : ℝ // 0 < r}) (g : AdelicGLn.AdelicGL K n) :
    centralSection K n s * g = g * centralSection K n s :=
  scalarUnits_mul_comm _ g


variable (K n) in
def detModule : AdelicGLn.AdelicGL K n →* {r : ℝ // 0 < r} :=
  (ideleModule K).comp (AdelicGLn.det K n)

theorem continuous_detModule : Continuous (detModule K n) :=
  continuous_ideleModule.comp (AdelicGLn.continuous_det K n)

theorem mem_normOneGL_iff_detModule {g : AdelicGLn.AdelicGL K n} :
    g ∈ normOneGL (K := K) (n := n) ↔ detModule K n g = 1 := by
  rw [mem_normOneGL]
  exact ⟨fun h => Subtype.ext (h.trans Positive.val_one.symm),
    fun h => (congrArg Subtype.val h).trans Positive.val_one⟩

theorem detModule_centralSection (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    detModule K n (centralSection K n s) = s := by
  refine Subtype.ext ?_
  have hd0 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : (detModule K n (centralSection K n s) : ℝ) =
      ∏ _i : Fin n, (ideleModule K (posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s)) : ℝ) := by
    rw [detModule, MonoidHom.comp_apply, centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply,
      scalarUnits_apply, det_diagUnits, map_prod, coe_finset_prod_pos]
  rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, posIdeleHom_apply,
    ideleModule_posIdele]
  change ((s.1 ^ ((n * Module.finrank ℚ K : ℝ))⁻¹) ^ Module.finrank ℚ K) ^ n = s.1
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le]
  have hne : (n * Module.finrank ℚ K : ℝ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hd0.ne')
  rw [show ((n * Module.finrank ℚ K : ℝ))⁻¹ * ((Module.finrank ℚ K * n : ℕ) : ℝ) = 1 by
    push_cast; field_simp, Real.rpow_one]

def glNormOneSplitting (hn : 0 < n) :
    AdelicGLn.AdelicGL K n ≃ₜ* normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} :=
  GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
    continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm (normOneGL (K := K) (n := n))
    (fun _ => mem_normOneGL_iff_detModule)

theorem exists_measure_eq_mul_measure_image (hn : 0 < n)
    [SecondCountableTopology (AdelicGLn.AdelicGL K n)] [MeasurableSpace (AdelicGLn.AdelicGL K n)]
    [BorelSpace (AdelicGLn.AdelicGL K n)]
    (μ₁ : Measure (normOneGL (K := K) (n := n))) [μ₁.IsHaarMeasure]
    (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ E : Set (normOneGL (K := K) (n := n)), MeasurableSet E →
      μ₁ E = c * μ ((fun p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval)) := by
  have : SecondCountableTopology (normOneGL (K := K) (n := n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  set Φ : AdelicGLn.AdelicGL K n ≃ₜ* normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} :=
    GroundTheory.Variant₂.N1.centralSplitting (detModule K n) continuous_detModule (centralSection K n)
      continuous_centralSection (detModule_centralSection hn) centralSection_mul_comm
      (normOneGL (K := K) (n := n)) (fun _ => mem_normOneGL_iff_detModule) with hΦ
  have hΦs : ∀ p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r},
      Φ.symm p = (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2 := fun p => rfl
  have hΦm : Measurable (Φ : AdelicGLn.AdelicGL K n → normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) :=
    Φ.continuous.measurable
  set lam : Measure (normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) := μ.map Φ with hlam
  have hlamH : lam.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ Φ
  have hν : posRealMeasure posRealUnitInterval = 1 := posRealMeasure_posRealUnitInterval
  set ρ : Measure (normOneGL (K := K) (n := n)) :=
    Measure.map Prod.fst (lam.restrict (Set.univ ×ˢ posRealUnitInterval)) with hρ
  have hρH : ρ.IsHaarMeasure := isHaarMeasure_map_fst_restrict lam posRealMeasure hν
  have hμ₁ : μ₁ = Measure.haarScalarFactor μ₁ ρ • ρ := Measure.isMulLeftInvariant_eq_smul μ₁ ρ
  refine ⟨(Measure.haarScalarFactor μ₁ ρ : ℝ≥0∞), ENNReal.coe_ne_top, fun E hE => ?_⟩
  have hS : MeasurableSet posRealUnitInterval := measurableSet_posRealUnitInterval
  have hρE : ρ E = μ (Φ ⁻¹' (E ×ˢ posRealUnitInterval)) := by
    rw [hρ, Measure.map_apply measurable_fst hE, Measure.restrict_apply (measurable_fst hE),
      hlam, Measure.map_apply hΦm]
    · congr 1
      ext p
      simp [and_comm]
    · exact (measurable_fst hE).inter (MeasurableSet.univ.prod hS)
  have himg : Φ ⁻¹' (E ×ˢ posRealUnitInterval) =
      (fun p : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} =>
        (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) '' (E ×ˢ posRealUnitInterval) := by
    ext g
    constructor
    · intro hg
      exact ⟨Φ g, hg, (hΦs (Φ g)).symm.trans (Φ.symm_apply_apply g)⟩
    · rintro ⟨p, hp, rfl⟩
      show Φ ((p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ∈ E ×ˢ posRealUnitInterval
      rw [← hΦs p, ContinuousMulEquiv.apply_symm_apply]
      exact hp
  have h1 : μ₁ E = (Measure.haarScalarFactor μ₁ ρ • ρ) E :=
    congrArg (fun m : Measure (normOneGL (K := K) (n := n)) => m E) hμ₁
  rw [h1, Measure.smul_apply, hρE, himg, ENNReal.smul_def, smul_eq_mul]

end Reduction

end

end GroundTheory.Automorphic
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

section Sums

variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]

def quotSum (Φ : G → M) : M :=
  ∑ᶠ q : G ⧸ H, Φ q.out

variable {H}

theorem quotSum_def (Φ : G → M) : quotSum H Φ = ∑ᶠ q : G ⧸ H, Φ q.out := rfl

theorem apply_out_mk {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hΦ g h h.2]

theorem quotSum_mul_left {Φ : G → M} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (x : G) :
    quotSum H (fun g => Φ (x * g)) = quotSum H Φ := by
  unfold quotSum
  calc ∑ᶠ q : G ⧸ H, Φ (x * q.out)
      = ∑ᶠ q : G ⧸ H, (fun q' : G ⧸ H => Φ q'.out) (MulAction.toPerm x q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm x q : G ⧸ H) = QuotientGroup.mk (x * q.out) := by
          rw [MulAction.toPerm_apply]
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        simp only [hq, apply_out_mk hΦ]
    _ = ∑ᶠ q : G ⧸ H, Φ q.out := finsum_comp_equiv (MulAction.toPerm x) (f := fun q' : G ⧸ H => Φ q'.out)

theorem quotSum_congr {Φ Ψ : G → M} (h : ∀ g, Φ g = Ψ g) : quotSum H Φ = quotSum H Ψ := by
  unfold quotSum
  exact finsum_congr fun q => h _

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quotSum (hH : IsOpen (H : Set G)) (hZH : Subgroup.center G ≤ H)
    {Φ : G → M} {C : Set G} (hC : IsCompact C)
    (hsupp : support Φ ⊆ (Subgroup.center G : Set G) * C) :
    (support fun q : G ⧸ H => Φ q.out).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine ((hC.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
  intro q hq
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp hq
  replace hzc : z * c = q.out := hzc
  refine ⟨c, hc, ?_⟩
  rw [← QuotientGroup.out_eq' q, ← hzc, QuotientGroup.eq]
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  rw [hzc', ← mul_assoc, inv_mul_cancel, one_mul]
  exact hZH hz

end Sums

section CompactModCenter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}


theorem IsCompactModCenter.comp_inv {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp (show g⁻¹ ∈ support φ from hg)
  replace hzc : z * c = g⁻¹ := hzc
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, by simpa using hc, ?_⟩
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  show z⁻¹ * c⁻¹ = g
  rw [← mul_inv_rev, ← hzc', hzc, inv_inv]

end CompactModCenter

end Parabolic

end GroundTheory.Automorphic
end
end
