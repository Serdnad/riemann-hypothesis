module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisCol

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem col_apply (i₀ : ι) (κ : GL ι 𝔸[k]) (j : ι) :
    TF.col i₀ κ j = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
  unfold TF.col
  rw [Matrix.mulVec_single_one]
  rfl

def finPart : 𝔸[k] →+* FiniteAdeleRing (𝓞 k) k := RingHom.snd _ _

theorem mem_OH_of_mem_intAd {x : 𝔸[k]} (hx : x ∈ intAd k) : x.2 ∈ OH k := by
  rw [mem_integralFiniteAdeles]
  intro v
  have := (Subring.mem_iInf.1 hx) v
  exact this

theorem sum_norm_sq {g : GL ι 𝔸[k]} {w : InfinitePlace k}
    (hg : (g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w) ∈ Matrix.unitaryGroup ι ℂ) (i₀ : ι) :
    ∑ j, ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hg) i₀) i₀
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  have h2 : ∀ j, (star ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w))) i₀ j *
      ((g : Matrix ι ι 𝔸[k]).map ((adStd k).φ w)) j i₀ =
      ((‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have e : ‖(adStd k).φ w ((g : Matrix ι ι 𝔸[k]) j i₀)‖ = ‖((g : Matrix ι ι 𝔸[k]) j i₀).1 w‖ :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
    rw [← e, Matrix.star_apply, Matrix.map_apply, mul_comm, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  simp only [h2] at h
  exact_mod_cast h

theorem stab_entry {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) {j : ι} (hj : j ≠ i₀) :
    (p : Matrix ι ι 𝔸[k]) j i₀ = 0 ∧ ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ = 0 :=
  hp j hj i₀ rfl

theorem stab_mul_inv {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (p : Matrix ι ι 𝔸[k]) i₀ i₀ * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ = 1 := by
  have h : ((p : Matrix ι ι 𝔸[k]) * ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀] at h
  · exact h
  · intro j _ hj
    rw [(stab_entry hp hj).2, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem bdet_single {R : Type} [CommRing R] {p : GL ι R} {i₀ : ι} (hu : IsUnit ((p : Matrix ι ι R) i₀ i₀)) :
    ((bdet {i₀} p : Rˣ) : R) = (p : Matrix ι ι R) i₀ i₀ := by
  have key : ∀ (i₁ : DecidableEq ({i₀} : Set ι)) (i₂ : Fintype ({i₀} : Set ι)),
      @Matrix.det _ i₁ i₂ R _ ((p : Matrix ι ι R).submatrix (Subtype.val : ({i₀} : Set ι) → ι) Subtype.val) =
        (p : Matrix ι ι R) i₀ i₀ := fun i₁ i₂ =>
    @Matrix.det_eq_elem_of_subsingleton _ i₁ i₂ R _ _ _ (⟨i₀, rfl⟩ : ({i₀} : Set ι))
  unfold bdet
  split_ifs with h
  · rw [IsUnit.unit_spec, key]
  · rw [key] at h
    exact absurd hu h

theorem bdet_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ((bdet {i₀} p : 𝔸[k]ˣ) : 𝔸[k]) = (p : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  bdet_single (IsUnit.of_mul_eq_one _ (stab_mul_inv hp))

theorem bdet_inv_val {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) = ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀ :=
  Units.inv_eq_of_mul_eq_one_right (by rw [bdet_val hp]; exact stab_mul_inv hp)

theorem col_mul {p : GL ι 𝔸[k]} {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) (κ : GL ι 𝔸[k]) :
    TF.col i₀ (p * κ) = (((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k]) • TF.col i₀ κ := by
  have h : ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1 =
      ((((bdet {i₀} p)⁻¹ : 𝔸[k]ˣ) : 𝔸[k])) • (Pi.single i₀ 1 : ι → 𝔸[k]) := by
    ext1 j
    have e : (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1) j =
        ((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) j i₀ := by
      rw [Matrix.mulVec_single_one]
      rfl
    rw [e, bdet_inv_val hp, Pi.smul_apply]
    by_cases hj : j = i₀
    · subst hj
      rw [Pi.single_eq_same, smul_eq_mul, mul_one]
    · rw [(stab_entry hp hj).2, Pi.single_eq_of_ne hj, smul_zero]
  unfold TF.col
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul]

theorem col_continuous (i₀ : ι) : Continuous fun κ : GL ι 𝔸[k] => TF.col i₀ κ := by
  unfold TF.col
  exact (Units.continuous_coe_inv).matrix_mulVec continuous_const

theorem col_one (i₀ : ι) : TF.col (k := k) i₀ 1 = Pi.single i₀ 1 := by
  unfold TF.col
  rw [inv_one, Units.val_one, Matrix.one_mulVec]

theorem col_unitVec {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    UnitVec (fun j => (TF.col i₀ κ j).1) := by
  intro w
  have h := sum_norm_sq ((((adStd k).kGL ι).inv_mem hκ).2 w) i₀
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  exact congrArg (fun x : 𝔸[k] => ‖x.1 w‖ ^ 2) (col_apply i₀ κ j)

theorem col_prim {κ : GL ι 𝔸[k]} (hκ : κ ∈ (adStd k).kGL ι) (i₀ : ι) :
    Prim fun j => (TF.col i₀ κ j).2 := by
  refine ⟨fun j => ?_, fun j => ((κ : Matrix ι ι 𝔸[k]) i₀ j).2, fun j => ?_, ?_⟩
  · exact Eq.mpr (congrArg (fun x : 𝔸[k] => x.2 ∈ OH k) (col_apply i₀ κ j))
      (mem_OH_of_mem_intAd (hκ.1 j i₀).2)
  · exact mem_OH_of_mem_intAd (hκ.1 i₀ j).1
  · have h : ((κ : Matrix ι ι 𝔸[k]) * ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k])) i₀ i₀ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at h
    have h2 := congrArg (finPart (k := k)) h

    rw [map_sum, map_one] at h2
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h2
    rw [map_mul]
    exact congrArg (fun x : 𝔸[k] => finPart ((κ : Matrix ι ι 𝔸[k]) i₀ j) * finPart x) (col_apply i₀ κ j)

theorem bdet_split {p : GL ι 𝔸[k]} (hk : p ∈ (adStd k).kGL ι) {i₀ : ι} (hp : p ∈ stab 𝔸[k] {i₀}) :
    ∃ (a : (InfiniteAdeleRing k)ˣ) (u : (FiniteAdeleRing (𝓞 k) k)ˣ), bdet {i₀} p = ofInfinite a * ofFinite u ∧
      (∀ w, ‖(a : InfiniteAdeleRing k) w‖ = 1) ∧ u ∈ finiteIntegralUnits k := by
  refine ⟨toInfinite k (bdet {i₀} p), toFinite k (bdet {i₀} p), ?_, fun w => ?_, ?_⟩
  · rw [mul_comm, ofFinite_mul_ofInfinite]
  · have hv : ((toInfinite k (bdet {i₀} p) : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 := by
      rw [← bdet_val hp]; rfl
    rw [hv]
    have h := sum_norm_sq (hk.2 w) i₀
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by
      rw [(stab_entry hp hj).1]
      show ‖(0 : w.Completion)‖ ^ 2 = 0
      simp)
      (fun h' => absurd (Finset.mem_univ _) h')] at h
    have h0 : 0 ≤ ‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ := norm_nonneg _
    nlinarith [h, h0, sq_nonneg (‖((p : Matrix ι ι 𝔸[k]) i₀ i₀).1 w‖ - 1)]
  · rw [mem_finiteIntegralUnits]
    intro v
    have h1 : ((toFinite k (bdet {i₀} p) : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        ((p : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_val hp]; rfl
    have h2 : (((toFinite k (bdet {i₀} p))⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) =
        (((p⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) i₀ i₀).2 := by
      rw [← bdet_inv_val hp, ← map_inv]; rfl
    rw [h1, h2]
    exact ⟨(mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).1)) v,
      (mem_integralFiniteAdeles.1 (mem_OH_of_mem_intAd (hk.1 i₀ i₀).2)) v⟩

theorem colLaw : ColLaw := by
  intro k _ _ ι _ _ i₀
  exact ⟨fun κ hκ => ⟨col_unitVec hκ i₀, col_prim hκ i₀⟩, col_continuous i₀, col_one i₀,
    fun p hk hp => ⟨col_mul hp, bdet_split hk hp⟩⟩

end GlobalTheory.CompanionTheory.EisCol
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped NumberField.AdeleRing nonZeroDivisors

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

variable {k : Type} [Field k] [NumberField k]

theorem ideleModule_ofFinite_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  have h : infiniteModule (ofFinite b : IdeleGroup k) = 1 :=
    Finset.prod_eq_one fun w _ ↦ by
      rw [show ((ofFinite b : IdeleGroup k) : 𝔸[k]).1 w = 1 from rfl, norm_one, one_pow]
  rw [ideleModule_apply, h, one_mul]

theorem norm_le_one_of_mem_OH {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (v : HeightOneSpectrum (𝓞 k)) :
    ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ ≤ 1 :=
  (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).1
      (mem_integralFiniteAdeles.1 hb v))

theorem finiteModule_le_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) : finiteModule (ofFinite b) ≤ 1 := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm _)]
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ norm_le_one_of_mem_OH hb v

theorem finiteModule_lt_one {b : (FiniteAdeleRing (𝓞 k) k)ˣ}
    (hb : (b : FiniteAdeleRing (𝓞 k) k) ∈ OH k) (hu : b ∉ finiteIntegralUnits k) :
    finiteModule (ofFinite b) < 1 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 k), ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ < 1 := by
    by_contra hcon
    push_neg at hcon
    refine hu ((mem_finiteIntegralUnits k).2 fun v ↦ ⟨mem_integralFiniteAdeles.1 hb v, ?_⟩)
    have hv1 : ‖(b : FiniteAdeleRing (𝓞 k) k) v‖ = 1 :=
      le_antisymm (norm_le_one_of_mem_OH hb v) (hcon v)
    have hmul : (b : FiniteAdeleRing (𝓞 k) k) v *
        ((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v = 1 :=
      congrArg (fun a : FiniteAdeleRing (𝓞 k) k ↦ a v) (Units.mul_inv b)
    have hn : ‖((b⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) v‖ = 1 := by
      have := congrArg norm hmul
      rwa [norm_mul, hv1, one_mul, norm_one] at this
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 k) k v).2
      ((Valued.toNormedField.norm_le_one_iff).1 hn.le)
  have hfin := finite_mulSupport_norm (ofFinite b : IdeleGroup k)
  have hvS : v ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
    exact hv.ne
  rw [finiteModule, finprod_eq_prod _ hfin, ← Finset.mul_prod_erase _ _ hvS]
  calc _ ≤ ‖((ofFinite b : IdeleGroup k) : 𝔸[k]).2 v‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun u _ ↦ norm_le_one_of_mem_OH hb u)
          (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

def integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) : ℂ :=
  g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (((n : ℝ) : ℝ) : ℂ)

theorem cpow_module_eq (b : (FiniteAdeleRing (𝓞 k) k)ˣ) (x : ℝ) :
    ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((finiteModule (ofFinite b) ^ x : ℝ) : ℂ) := by
  rw [ideleModule_ofFinite_eq, Complex.ofReal_cpow (finiteModule_pos _).le]

theorem norm_integrand (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ) (ω : HeckeCharacter k) (n : ℕ)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ = ‖g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)‖ *
      finiteModule (ofFinite b) ^ (n : ℝ) := by
  rw [integrand, cpow_module_eq, norm_mul, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (finiteModule_pos _).le _)]

theorem continuous_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) (ω : HeckeCharacter k) (n : ℕ) :
    Continuous (integrand g ω n) := by
  have h1 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      g fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k) :=
    ((GJMatrix.mem_finiteSchwartzBruhatPi k).1 hg).1.continuous.comp
      (continuous_pi fun _ ↦ Units.continuous_val)
  have h2 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ (ω.toIdele (ofFinite b) : ℂ) :=
    continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_ofFinite)
  have h3 : Continuous fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦
      ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      ((continuous_finiteModule.comp continuous_ofFinite).rpow_const
        fun b ↦ Or.inl (finiteModule_pos _).ne')
  have : integrand g ω n = fun b : (FiniteAdeleRing (𝓞 k) k)ˣ ↦ g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) *
      (ω.toIdele (ofFinite b) : ℂ) * ((finiteModule (ofFinite b) ^ (n : ℝ) : ℝ) : ℂ) := by
    funext b
    rw [integrand, cpow_module_eq]
  rw [this]
  exact (h1.mul h2).mul h3

theorem norm_integrand_le {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} (ω : HeckeCharacter k)
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k)) {n : ℕ} (hn : 2 ≤ n)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    ‖integrand g ω n b‖ ≤ finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2 b := by
  rw [norm_integrand]
  by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
  · rw [h0, norm_zero, zero_mul]
    exact finiteZetaBound_nonneg _ _ _
  have hO := (hb _).2 h0
  have hL : (b : FiniteAdeleRing (𝓞 k) k) ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) := by
    rw [← SetLike.mem_coe, idealFiniteAdeles_one]
    exact hO
  rw [finiteZetaBound, if_pos hL]
  have hpow : finiteModule (ofFinite b) ^ (n : ℝ) ≤ finiteModule (ofFinite b) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (finiteModule_pos _) (finiteModule_le_one hO)
      (by exact_mod_cast hn)
  calc _ ≤ 1 * finiteModule (ofFinite b) ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_right (hb _).1 (Real.rpow_nonneg (finiteModule_pos _).le _)
    _ ≤ _ := by rwa [one_mul]

theorem tendsto_integrand {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ} {ω : HeckeCharacter k}
    (hb : ∀ t, ‖g fun _ ↦ t‖ ≤ 1 ∧ (g (fun _ ↦ t) ≠ 0 → t ∈ OH k))
    (hu : ∀ u ∈ finiteIntegralUnits k,
      g (fun _ ↦ (u : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite u) : ℂ) = 1)
    (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    Tendsto (fun n ↦ integrand g ω n b) atTop
      (𝓝 (((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b)) := by
  by_cases hW : b ∈ finiteIntegralUnits k
  · rw [Set.indicator_of_mem (SetLike.mem_coe.2 hW)]
    have hm : finiteModule (ofFinite b : IdeleGroup k) = 1 := finiteModule_eq_one_of_mem hW
    refine tendsto_const_nhds.congr fun n ↦ ?_
    rw [integrand, cpow_module_eq, hu b hW, hm, Real.one_rpow, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem (fun h ↦ hW (SetLike.mem_coe.1 h))]
    by_cases h0 : g (fun _ ↦ (b : FiniteAdeleRing (𝓞 k) k)) = 0
    · refine tendsto_const_nhds.congr fun n ↦ ?_
      rw [integrand, h0, zero_mul, zero_mul]
    have hlt := finiteModule_lt_one ((hb _).2 h0) hW
    refine squeeze_zero_norm (a := fun n : ℕ ↦ finiteModule (ofFinite b) ^ n) (fun n ↦ ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (finiteModule_pos _).le hlt)
    rw [norm_integrand, Real.rpow_natCast]
    calc _ ≤ 1 * finiteModule (ofFinite b) ^ n :=
          mul_le_mul_of_nonneg_right (hb _).1 (pow_nonneg (finiteModule_pos _).le _)
      _ = _ := one_mul _

theorem zFinLim : ZFinLim := by
  intro k _ _ g ω hg hb hu B
  have hlim : Tendsto (fun n : ℕ ↦ ∫ b, integrand g ω n b ∂finiteIdeleMeasure k) atTop
      (𝓝 (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
        Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k)) :=
    tendsto_integral_filter_of_dominated_convergence
      (finiteZetaBound (1 : (FractionalIdeal (𝓞 k)⁰ k)ˣ) 2)
      (Eventually.of_forall fun n ↦ (continuous_integrand hg ω n).aestronglyMeasurable)
      ((eventually_ge_atTop 2).mono fun n hn ↦ Eventually.of_forall (norm_integrand_le ω hb hn))
      (integrable_finiteZetaBound 1 (by norm_num))
      (Eventually.of_forall (tendsto_integrand hb hu))
  have hval : (∫ b, ((finiteIntegralUnits k : Subgroup (FiniteAdeleRing (𝓞 k) k)ˣ) :
      Set (FiniteAdeleRing (𝓞 k) k)ˣ).indicator (fun _ ↦ (1 : ℂ)) b ∂finiteIdeleMeasure k) = 1 := by
    rw [integral_indicator_const _ (isOpen_finiteIntegralUnits k).measurableSet, Measure.real,
      finiteIdeleMeasure_finiteIntegralUnits]
    simp
  rw [hval] at hlim
  obtain ⟨n, hn, hB⟩ := ((hlim.eventually_ne one_ne_zero).and
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop B)).exists
  exact ⟨n, hB, hn⟩

end GlobalTheory.CompanionTheory.EisTF
end
end

section

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisTestFun

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup PositivityTheory.RgEis PositivityTheory.RgEis.TF

variable {k : Type} [Field k] [NumberField k]

theorem continuous_infinite_idele_inclusion :
    Continuous (ofInfinite : (InfiniteAdeleRing k)ˣ → IdeleGroup k) :=
  (ContinuousMulEquiv.symm (prodEquiv k)).continuous.comp (Continuous.prodMk_left 1)

theorem ideleModule_ofInfinite_eq (a : (InfiniteAdeleRing k)ˣ) :
    (ideleModule k (ofInfinite a) : ℝ) = ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ w.mult := by
  have h1 : ∀ w, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).1 w = (a : InfiniteAdeleRing k) w := fun w => by
    have := congrArg (fun u : (InfiniteAdeleRing k)ˣ => (u : InfiniteAdeleRing k) w) (toInfinite_ofInfinite a)
    exact this
  have h2 : ∀ v, ((ofInfinite a : IdeleGroup k) : 𝔸[k]).2 v = 1 := fun v => by
    have := congrArg (fun u : (FiniteAdeleRing (𝓞 k) k)ˣ => (u : FiniteAdeleRing (𝓞 k) k) v) (toFinite_ofInfinite a)
    exact this
  rw [ideleModule_eq]
  simp only [h1, h2, norm_one, finprod_one, mul_one]

theorem exists_norm_rd_le (φ : 𝓢(Unit → mixedSpace k, ℂ)) (K : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x : InfiniteAdeleRing k,
      ‖rd φ (fun _ => x)‖ ≤ C * ∏ w, ((1 + ‖x w‖) ^ K)⁻¹ := by
  let e : mixedSpace k ≃L[ℝ] (Unit → mixedSpace k) :=
    (ContinuousLinearEquiv.funUnique Unit ℝ (mixedSpace k)).symm
  obtain ⟨C, hC, h⟩ := exists_norm_schwartz_le_prod (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) K
  refine ⟨C, hC, fun x => ?_⟩
  have hx := h x
  have he : (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) (homeomorphMixedSpace k x) =
      rd φ (fun _ => x) := by
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, rd]
    congr 1
  rwa [he] at hx

theorem module_rpow_eq (a : (InfiniteAdeleRing k)ˣ) (x : ℝ) :
    (ideleModule k (ofInfinite a) : ℝ) ^ x =
      ∏ w : InfinitePlace k, ‖(a : InfiniteAdeleRing k) w‖ ^ ((w.mult : ℝ) * x) := by
  rw [ideleModule_ofInfinite_eq, ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]

theorem integrable_norm_rd_mul (φ : 𝓢(Unit → mixedSpace k, ℂ)) {x : ℝ} (hx : 1 < x)
    (hc : Continuous fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x) :
    Integrable (fun a : (InfiniteAdeleRing k)ˣ =>
      ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x)
      (infiniteIdeleMeasure k) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * x + 2)
  obtain ⟨C, hC, h⟩ := exists_norm_rd_le φ K
  refine Integrable.mono' ((integrable_infiniteZetaBound (K := k) hx.le hK).const_mul C)
    hc.aestronglyMeasurable (Eventually.of_forall fun a => ?_)
  have hm : 0 ≤ (ideleModule k (ofInfinite a) : ℝ) ^ x := Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hm)]
  calc ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x
      ≤ (C * ∏ w, ((1 + ‖(a : InfiniteAdeleRing k) w‖) ^ K)⁻¹) * (ideleModule k (ofInfinite a) : ℝ) ^ x :=
        mul_le_mul_of_nonneg_right (h a) hm
    _ = C * infiniteZetaBound x K a := by
        rw [module_rpow_eq, infiniteZetaBound, mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_eq_mul_inv, mul_comm]

theorem zInf_ne_zero : ZInf := by
  intro k _ _ φ ω h h1 x hx
  have hc0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => rd φ (fun _ => (a : InfiniteAdeleRing k)) :=
    φ.continuous.comp (continuous_pi fun _ =>
      (homeomorphMixedSpace k).continuous.comp Units.continuous_val)
  have hm0 : Continuous fun a : (InfiniteAdeleRing k)ˣ => (ideleModule k (ofInfinite a) : ℝ) :=
    continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp continuous_infinite_idele_inclusion)
  set f : (InfiniteAdeleRing k)ˣ → ℝ := fun a =>
    ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ * (ideleModule k (ofInfinite a) : ℝ) ^ x with hf
  have hcf : Continuous f :=
    hc0.norm.mul (hm0.rpow_const fun _ => Or.inr (by linarith))
  have hint : Integrable f (infiniteIdeleMeasure k) := integrable_norm_rd_mul φ hx hcf
  have hnn : 0 ≤ f := fun a => mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (ideleModule k (ofInfinite a)).2.le _)
  have hpt : ∀ a : (InfiniteAdeleRing k)ˣ,
      rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
        ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ (x : ℂ) = ((f a : ℝ) : ℂ) := fun a => by
    obtain ⟨r, hr, e⟩ := h a
    have hn : r = ‖rd φ (fun _ => (a : InfiniteAdeleRing k))‖ := by
      have := congrArg norm e
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hr] at this
      exact this.symm
    rw [e, hn, hf]
    push_cast
    rw [Complex.ofReal_cpow (ideleModule k (ofInfinite a)).2.le]
  have hz : zInf φ ω x = ((∫ a, f a ∂infiniteIdeleMeasure k : ℝ) : ℂ) := by
    rw [zInf, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  have hpos : 0 < ∫ a, f a ∂infiniteIdeleMeasure k := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    have hop : IsOpen (Function.support f) := isOpen_compl_singleton.preimage hcf
    refine hop.measure_pos _ ⟨1, ?_⟩
    have hm1 : 0 < (ideleModule k (ofInfinite (1 : (InfiniteAdeleRing k)ˣ)) : ℝ) ^ x :=
      Real.rpow_pos_of_pos (ideleModule k (ofInfinite _)).2 _
    have : f 1 ≠ 0 := by
      simp only [hf, Units.val_one]
      exact mul_ne_zero (norm_ne_zero_iff.2 h1) hm1.ne'
    exact this
  rw [hz]
  exact_mod_cast hpos.ne'

end GlobalTheory.CompanionTheory.EisTestFun
end
end
