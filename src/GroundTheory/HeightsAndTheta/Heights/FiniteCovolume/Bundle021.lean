module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle017
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.ClassNumber
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

section Numbers

variable {E : Type*} [Field E] [NumberField E]

def scaledIdeal (I : AddSubgroup E) (hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) (b : E) :
    Ideal (𝓞 E) where
  carrier := {y | b⁻¹ * (y : E) ∈ I}
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_ofPred_eq] at *
    have h := I.add_mem hy hz
    convert h using 1
    push_cast
    ring
  zero_mem' := by simp [I.zero_mem]
  smul_mem' := by
    intro a y hy
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    have h := hI a _ hy
    convert h using 1
    push_cast
    ring

theorem mem_scaledIdeal {I : AddSubgroup E} {hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I} {b : E}
    {y : 𝓞 E} : y ∈ scaledIdeal I hI b ↔ b⁻¹ * (y : E) ∈ I := Iff.rfl

end Numbers

theorem IdealClassesFinite.proof (E) [Field E] [NumberField E] : IdealClassesFinite.Statement E := by
  classical
  let rep : ClassGroup (𝓞 E) → nonZeroDivisors (Ideal (𝓞 E)) := fun c => (ClassGroup.mk0_surjective c).choose
  have hrep : ∀ c, ClassGroup.mk0 (rep c) = c := fun c => (ClassGroup.mk0_surjective c).choose_spec
  let J : ClassGroup (𝓞 E) → AddSubgroup E := fun c =>
    ((rep c : Ideal (𝓞 E)).toAddSubgroup).map (algebraMap (𝓞 E) E).toAddMonoidHom
  refine ⟨Set.range J, Set.finite_range J, ?_⟩
  intro I hfg hne hI
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨⟨b, hb0⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (S : Finset E)
  have hbne : (b : E) ≠ 0 := by
    have : b ≠ 0 := nonZeroDivisors.ne_zero hb0
    exact_mod_cast this
  have hint : ∀ x ∈ I, ∃ w : 𝓞 E, (w : E) = b * x := by
    have hall : ∀ t : I, ∃ w : 𝓞 E, (w : E) = b * (t : E) := by
      intro t
      have ht : t ∈ AddSubsemigroup.closure (S : Set I) := by rw [hS]; trivial
      induction ht using AddSubsemigroup.closure_induction with
      | mem t ht =>
        obtain ⟨w, hw⟩ := hb t (by simpa using Finset.mem_image_of_mem Subtype.val ht)
        exact ⟨w, by rw [Algebra.smul_def] at hw; exact hw⟩
      | add x y _ _ hx hy =>
        obtain ⟨w, hw⟩ := hx
        obtain ⟨v, hv⟩ := hy
        exact ⟨w + v, by push_cast; linear_combination hw + hv⟩
    intro x hx
    exact hall ⟨x, hx⟩
  let 𝔞 := scaledIdeal I hI (b : E)
  have hmem : ∀ z ∈ I, ∀ w : 𝓞 E, (w : E) = b * z → w ∈ 𝔞 := by
    intro z hz w hw
    rw [mem_scaledIdeal, hw, ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
    exact hz
  have h𝔞 : 𝔞 ∈ nonZeroDivisors (Ideal (𝓞 E)) := by
    apply mem_nonZeroDivisors_of_ne_zero
    obtain ⟨z, hz, hz0⟩ := (AddSubgroup.bot_or_exists_ne_zero I).resolve_left hne
    obtain ⟨w, hw⟩ := hint z hz
    intro h0
    have hw𝔞 : w ∈ 𝔞 := hmem z hz w hw
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at hw𝔞
    rw [hw𝔞] at hw
    push_cast at hw
    exact hz0 ((mul_eq_zero.1 hw.symm).resolve_left hbne)
  set c := ClassGroup.mk0 ⟨𝔞, h𝔞⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hrep c).symm
  have hxE : (x : E) ≠ 0 := by exact_mod_cast hx
  have hyE : (y : E) ≠ 0 := by exact_mod_cast hy
  refine ⟨J c, ⟨c, rfl⟩, (y : E) / ((x : E) * b), div_ne_zero hyE (mul_ne_zero hxE hbne), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hint z hz
    have hxw : x * w ∈ Ideal.span {y} * (rep c : Ideal (𝓞 E)) :=
      hxy ▸ Ideal.mem_span_singleton_mul.2 ⟨w, hmem z hz w hw, rfl⟩
    obtain ⟨v, hv, hvw⟩ := Ideal.mem_span_singleton_mul.1 hxw
    have hvw' : (y : E) * v = x * (b * z) := by
      rw [← hw]; exact_mod_cast hvw
    refine AddSubgroup.mem_map.2 ⟨(v : E), AddSubgroup.mem_map.2 ⟨v, hv, rfl⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
    linear_combination hvw'
  · intro hz
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hz
    obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.1 hu
    have hyv : y * v ∈ Ideal.span {x} * 𝔞 :=
      hxy.symm ▸ Ideal.mem_span_singleton_mul.2 ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := Ideal.mem_span_singleton_mul.1 hyv
    have hwv' : (x : E) * w = y * v := by exact_mod_cast hwv
    rw [mem_scaledIdeal] at hw
    convert hw using 1
    simp only [AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    field_simp
    linear_combination -hwv'

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem archEmbed_injective (h : HermitianForm F E W) (v : Basis ι E W) :
    Function.Injective (archEmbed h v) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  have h1 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E).map w.embedding = 1 :=
    congrArg
      (fun g : archUnitary h v => (((g : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) : Matrix ι ι ℂ)) hγ
  have h2 : ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) = 1 := by
    ext i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at this
    apply w.embedding.injective
    rw [this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : unitaryGroupEquivMatrix h v γ = 1 := Subtype.ext (Units.ext h2)
  rwa [MulEquiv.map_eq_one_iff] at h3

theorem countable_unitaryGroup (h : HermitianForm F E W) (v : Basis ι E W) :
    Countable h.unitaryGroup := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix ι ι E) := inferInstanceAs (Countable (ι → ι → E))
  refine Function.Injective.countable (f := fun γ : h.unitaryGroup =>
    ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E)) ?_
  intro a b hab
  exact (unitaryGroupEquivMatrix h v).injective (Subtype.ext (Units.ext hab))

theorem AdelicCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    [FiniteDimensional E W] (h₁ : LatticeOrbitsFinite.Statement h)
    (h₂ : ArithmeticCovolumeFinite.Statement h v) (h₃ : ArchimedeanUnitaryEquiv.Statement h v)
    (h₄ : AdelicLatticeDictionary.Statement h v)
    (h₅ : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v := by
  classical
  intro μ _
  obtain ⟨ψ, hψ⟩ := h₃
  obtain ⟨K, D, L, hKc, hKo, hLD, hLeq, hLinj⟩ := h₄
  let e : unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ×
      unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) ≃ₜ*
      archUnitary h v × unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) :=
    { toMulEquiv := MulEquiv.prodCongr ψ.toMulEquiv (MulEquiv.refl _)
      continuous_toFun := (ψ.continuous.comp continuous_fst).prodMk continuous_snd
      continuous_invFun := (ψ.symm.continuous.comp continuous_fst).prodMk continuous_snd }
  let Φ := (adeleSplit h v).trans e
  have hΦ₁ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).1 = archEmbed h v γ :=
    fun γ => hψ γ
  have hΦ₂ : ∀ γ : h.unitaryGroup, (Φ (hermitianDiagonal h v γ)).2 =
      (adeleSplit h v (hermitianDiagonal h v γ)).2 := fun γ => rfl
  haveI := countable_unitaryGroup h v
  haveI : Countable (hermitianDiagonal h v).range := by
    refine Function.Surjective.countable (f := fun γ : h.unitaryGroup =>
      (⟨hermitianDiagonal h v γ, γ, rfl⟩ : (hermitianDiagonal h v).range)) ?_
    rintro ⟨_, γ, rfl⟩
    exact ⟨γ, rfl⟩

  obtain ⟨S₀, hS₀, hS₀cov⟩ := h₁ D
  let r : AddSubgroup W → unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F) := fun L₀ => if hL : ∃ y, L y = L₀ then hL.choose else 1
  have hr : ∀ y, L (r (L y)) = L y := fun y => by
    have hL : ∃ y', L y' = L y := ⟨y, rfl⟩
    simp only [r, dif_pos hL]
    exact hL.choose_spec

  have hstab : ∀ (γ : h.unitaryGroup) (s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F)),
      γ ∈ latticeStab h (L s) ↔ s⁻¹ * (Φ (hermitianDiagonal h v γ)).2 * s ∈ K := by
    intro γ s
    rw [latticeStab, MulAction.mem_stabilizer_iff, hΦ₂, ← hLeq, eq_comm, hLinj, mul_assoc]
  have hslice : ∀ s : unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F), sliceGroup Φ (hermitianDiagonal h v).range K s =
      archLatticeGroup h v (L s) := by
    intro s
    ext x
    rw [mem_sliceGroup, archLatticeGroup, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨γ, rfl⟩, hk, rfl⟩
      exact ⟨γ, (hstab γ s).2 hk, (hΦ₁ γ).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hermitianDiagonal h v γ, ⟨γ, rfl⟩, (hstab γ s).1 hγ, hΦ₁ γ⟩
  obtain ⟨FD, hFD, hfin⟩ := h₅ Φ (hermitianDiagonal h v).range K (hS₀.toFinset.image r) hKc hKo
    (by
      rintro _ ⟨γ, rfl⟩ h1
      rw [hΦ₁, ← (archEmbed h v).map_one] at h1
      rw [archEmbed_injective h v h1, map_one])
    (by
      intro y
      obtain ⟨L₀, hL₀, g, hg⟩ := hS₀cov (L y) (hLD y)
      have hL₀' : L₀ = L ((adeleSplit h v (hermitianDiagonal h v g⁻¹)).2 * y) := by
        rw [hLeq, ← hg, smul_smul, inv_mul_cancel, one_smul]
      have hs : L (r L₀) = L₀ := by rw [hL₀']; exact hr _
      have hk : ((Φ (hermitianDiagonal h v g)).2 * r L₀)⁻¹ * y ∈ K := by
        rw [← hLinj, hΦ₂, hLeq, hs, hg]
      refine ⟨hermitianDiagonal h v g, ⟨g, rfl⟩, r L₀, ?_, _, hk, ?_⟩
      · exact Finset.mem_image_of_mem r (hS₀.mem_toFinset.2 hL₀)
      · group)
    (by
      intro s _ μ₁ _
      rw [hslice s]
      exact h₂ μ₁ D (L s) (hLD s))
    μ
  exact ⟨FD, hFD, hfin⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_posDef_mul_inv_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (hdet : IsUnit H.det) :
    ∃ P : Matrix n n ℂ, P.PosDef ∧ P * H⁻¹ * P = H := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set d : n → ℝ := hH.eigenvalues with hddef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    have h0 := hdet.ne_zero
    rw [hH.det_eq_prod_eigenvalues] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [← hddef, hi]))
  have hinv : H⁻¹ = U * diagonal (fun i => (((d i)⁻¹ : ℝ) : ℂ)) * star U := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
      diagonal_mul_diagonal]
    have : (fun i => ((d i : ℝ) : ℂ) * (((d i)⁻¹ : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hd i), Complex.ofReal_one]
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨U * diagonal (fun i => ((|d i| : ℝ) : ℂ)) * star U, ?_, ?_⟩
  · have hD : (diagonal (fun i => ((|d i| : ℝ) : ℂ))).PosDef :=
      Matrix.posDef_diagonal_iff.mpr fun i => Complex.zero_lt_real.mpr (abs_pos.mpr (hd i))
    have hinj : Function.Injective U.vecMul := by
      intro x y hxy
      have := congrArg (fun z => z ᵥ* star U) hxy
      simpa only [vecMul_vecMul, hUU', vecMul_one] using this
    simpa only [star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same hinj
  · rw [hinv]
    conv_rhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (star U) U, hUU,
      Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal,
      ← Matrix.mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
    congr 3
    funext i
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc |d i| * (d i)⁻¹ * |d i| = |d i| * |d i| * (d i)⁻¹ := by ring
      _ = d i * d i * (d i)⁻¹ := by rw [abs_mul_abs_self]
      _ = d i := mul_inv_cancel_right₀ (hd i) _

section Spaces

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem MajorantExists.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : GramAtData.Statement h v) : MajorantExists.Statement h v := by
  choose P hP hPH using fun w => exists_posDef_mul_inv_mul_eq (h₁ w).1 (h₁ w).2
  exact ⟨⟨P, hP, hPH⟩⟩

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
