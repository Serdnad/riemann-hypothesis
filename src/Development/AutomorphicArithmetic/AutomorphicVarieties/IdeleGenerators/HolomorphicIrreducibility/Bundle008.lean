module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle001
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix

namespace UpperTheory.V.Sd

private def ee {V : Type} [Fintype V] (μ x : V → ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ))

private theorem ee_add {V : Type} [Fintype V] (μ x y : V → ℝ) : ee μ (x + y) = ee μ x * ee μ y := by
  simp only [ee, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib, Complex.exp_add]

private theorem ee_add' {V : Type} [Fintype V] (μ ν x : V → ℝ) : ee (μ + ν) x = ee μ x * ee ν x := by
  simp only [ee, Pi.add_apply, Complex.ofReal_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.exp_add]

private theorem ee_zero {V : Type} [Fintype V] (μ : V → ℝ) : ee μ 0 = 1 := by simp [ee]

private theorem ee_zero' {V : Type} [Fintype V] (x : V → ℝ) : ee 0 x = 1 := by simp [ee]

private theorem norm_ee {V : Type} [Fintype V] (μ x : V → ℝ) : ‖ee μ x‖ = 1 := by
  have : (2 * Real.pi * Complex.I * ∑ v, (μ v : ℂ) * (x v : ℂ)) = ((2 * Real.pi * ∑ v, μ v * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

private theorem exists_ee {V : Type} [Fintype V] (μ : V → ℝ) (h : μ ≠ 0) : ∃ g, ee μ g = -1 := by
  classical
  obtain ⟨v, hv⟩ := Function.ne_iff.1 h
  have hv' : (μ v : ℂ) ≠ 0 := by exact_mod_cast hv
  refine ⟨Pi.single v (1 / (2 * μ v)), ?_⟩
  have : ∑ w, (μ w : ℂ) * ((Pi.single v (1 / (2 * μ v)) : V → ℝ) w : ℂ) = 1 / 2 := by
    rw [Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]; push_cast; field_simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  rw [ee, this, ← Complex.exp_pi_mul_I]
  congr 1; ring

private theorem hs_congr {ι : Type} {f g : ι → ℂ} {d : ℂ} (h : HasSum f d) (e : ∀ i, g i = f i) : HasSum g d :=
  (funext e : g = f) ▸ h

private theorem kill {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) d) (S : Finset ι) :
    ∃ C : ι → ℂ, (∀ i, ‖C i‖ ≤ ‖B i‖) ∧ (∀ i ∈ S, C i = 0) ∧ ∀ x, HasSum (fun i => C i * ee (μ i) x) d := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨B, fun _ => le_rfl, by simp, h⟩
  | insert j S _ ih =>
    obtain ⟨C, h1, h2, h3⟩ := ih
    by_cases hj : B j = 0
    · refine ⟨C, h1, fun i hi => ?_, h3⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · simpa [hj] using h1 i
      · exact h2 i hi
    obtain ⟨g, hg⟩ := exists_ee (μ j) (hμ j hj)
    refine ⟨fun i => C i * ((1 + ee (μ i) g) / 2), fun i => ?_, fun i hi => ?_, fun x => ?_⟩
    · have : ‖(1 + ee (μ i) g) / 2‖ ≤ 1 := by
        have := norm_add_le 1 (ee (μ i) g)
        rw [norm_ee, norm_one] at this
        rw [norm_div, Complex.norm_two]; linarith
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) this).trans (h1 i)
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · simp [hg]
      · simp [h2 i hi]
    · have := ((h3 x).add (h3 (x + g))).div_const 2
      rw [show (d + d) / 2 = d by ring] at this
      refine hs_congr this fun i => ?_
      rw [ee_add]; ring

private theorem const_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (d : ℂ) (hμ : ∀ i, B i ≠ 0 → μ i ≠ 0)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) d) : d = 0 := by
  have hs : Summable fun i => ‖B i‖ := by
    have := (h 0).summable
    simp only [ee_zero, mul_one] at this
    exact this.norm
  have ht := tendsto_tsum_compl_atTop_zero (fun i => ‖B i‖)
  have : ‖d‖ ≤ 0 := by
    refine ge_of_tendsto' ht fun S => ?_
    obtain ⟨C, h1, h2, h3⟩ := kill μ B d hμ h S
    have h4 := h3 0
    simp only [ee_zero, mul_one] at h4
    have h5 : HasSum (fun i : {x // x ∉ S} => C i) d := by
      refine (hasSum_subtype_iff_of_support_subset (s := {x | x ∉ S}) ?_).2 h4
      intro i hi hS
      exact hi (h2 i hS)
    exact h5.norm_le_of_bounded (hs.subtype _).hasSum fun i => h1 i
  simpa using this

private theorem coef_zero {V ι : Type} [Fintype V] (μ : ι → V → ℝ) (B : ι → ℂ) (hμ : Function.Injective μ)
    (h : ∀ x, HasSum (fun i => B i * ee (μ i) x) 0) (j : ι) : B j = 0 := by
  classical
  have := const_zero (fun i => μ i - μ j) (fun i => if i = j then 0 else B i) (-B j) (fun i hi => ?_) fun x => ?_
  · simpa using this
  · have : i ≠ j := by rintro rfl; simp at hi
    exact sub_ne_zero.2 (hμ.ne this)
  · have := ((h x).mul_right (ee (-μ j) x)).sub (hasSum_ite_eq j (B j))
    rw [zero_mul, zero_sub] at this
    refine hs_congr this fun i => ?_
    rw [mul_assoc, ← ee_add', ← sub_eq_add_neg]
    by_cases hi : i = j
    · subst hi; simp [ee_zero']
    · simp [hi]

variable {F : Type} [Field F] [NumberField F]

private theorem genD_unique {y : Af F} {𝔪 𝔫 : Ideal (𝓞 F)} (h : GenD y 𝔪) (h' : GenD y 𝔫) : 𝔪 = 𝔫 := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 F), ordI w 𝔪 = ordI w 𝔫 := fun w => by
    have := (h.2 w).symm.trans (h'.2 w)
    rw [WithZero.exp_inj] at this
    omega
  rw [← Ideal.finprod_heightOneSpectrum_factorization h.1, ← Ideal.finprod_heightOneSpectrum_factorization h'.1]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (hc w)

private theorem coefAt_eq {y : Af F} {𝔪 : Ideal (𝓞 F)} (h : GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = a 𝔪 := by
  have h' : ∃ 𝔪, GenD y 𝔪 := ⟨𝔪, h⟩
  rw [coefAt, dite_eq_left h', genD_unique h'.choose_spec h]

private theorem ordI_fin {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ordI w I = 0 := by
  have := Associates.finite_factors (R := 𝓞 F) hI
  filter_upwards [this] with w hw
  exact_mod_cast hw

private theorem exists_genD {𝔪 : Ideal (𝓞 F)} (h : 𝔪 ≠ ⊥) : ∃ y : (Af F)ˣ, GenD (y : Af F) 𝔪 := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuedAdicCompletion_surjective F
    (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ)))
  have hf : ∀ᶠ w in Filter.cofinite, Valued.v (t w) = 1 := by
    filter_upwards [ordI_fin h, ordI_fin (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w h1 h2
    rw [ht, h1, h2]; simp
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hw.le⟩
  have hu : IsUnit a := FiniteAdeleRing.isUnit_iff.2 ⟨fun w hw => by
    have := ht w
    rw [show t w = 0 from hw, map_zero] at this
    exact WithZero.exp_ne_zero this.symm, hf⟩
  exact ⟨hu.unit, h, fun w => ht w⟩

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.expUnique :
    UpperTheory.V.Sd.ExpUnique := by
  intro F _ _ _ φ k c₀ c₀' a a' h h'
  have key : ∀ (yf : (Af F)ˣ) (x : InfinitePlace F → ℝ),
      HasSum (fun ξ : {ξ : F // ∀ v, 0 < reAt v ξ} =>
        ((coefAt a (algebraMap F (Af F) ξ.1 * (yf : Af F)) - coefAt a' (algebraMap F (Af F) ξ.1 * (yf : Af F))) *
          Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * Complex.I)) * ee (fun v => reAt v ξ.1) x)
        (c₀' yf - c₀ yf) := by
    intro yf x
    have := (h x 1 (by simp) yf).sub (h' x 1 (by simp) yf)
    rw [sub_sub_sub_cancel_left] at this
    refine hs_congr this fun ξ => ?_
    rw [← sub_mul, mul_assoc, ee, ← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
    congr 3
    refine Finset.sum_congr rfl fun v _ => ?_
    simp; ring
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hc : ∀ yf, c₀' yf - c₀ yf = 0 := fun yf =>
    const_zero _ _ _ (fun ξ _ h0 => (ξ.2 v₀).ne' (congrFun h0 v₀)) (key yf)
  refine ⟨funext fun yf => (sub_eq_zero.1 (hc yf)).symm, fun 𝔪 hm => ?_⟩
  obtain ⟨y, hy⟩ := exists_genD hm
  have hinj : Function.Injective fun (ξ : {ξ : F // ∀ v, 0 < reAt v ξ}) (v : InfinitePlace F) => reAt v ξ.1 := by
    intro ξ η he
    have h1 : reAt v₀ ξ.1 = reAt v₀ η.1 := congrFun he v₀
    have hr := IsTotallyReal.isReal v₀
    refine Subtype.ext (v₀.embedding.injective ?_)
    rw [← InfinitePlace.embedding_of_isReal_apply hr, ← InfinitePlace.embedding_of_isReal_apply hr]
    simp only [reAt, ← InfinitePlace.embedding_of_isReal_apply hr, Complex.ofReal_re] at h1
    rw [h1]
  have := coef_zero _ _ hinj (fun x => hc y ▸ key y x) ⟨1, fun v => by simp [reAt]⟩
  simp only [map_one, one_mul, mul_eq_zero, Complex.exp_ne_zero, or_false] at this
  rw [coefAt_eq hy, coefAt_eq hy] at this
  exact sub_eq_zero.1 this
end
end

section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem eisReg_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  let R : Subring Ω := (Int.castRingHom Ω).range
  have hI : Ideal.span {((p : ℕ) : R)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, k, rfl⟩, hk⟩
    have h1 : ((p : ℕ) : Ω) * ((k : ℤ) : Ω) = 1 := congrArg Subtype.val hk
    have h2 : ((p : ℕ) : ℤ) * k = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : R), Ideal.mem_span_singleton_self _, by simp⟩)⟩

private theorem eisReg_charpoly {K : Type} [Field K] (g r : GL (Fin 2) K) (a b : K)
    (h : ∀ i j, j < i → (g * r * g⁻¹ : GL (Fin 2) K) i j = 0)
    (ha : (g * r * g⁻¹ : GL (Fin 2) K) 0 0 = a) (hb : (g * r * g⁻¹ : GL (Fin 2) K) 1 1 = b) :
    (r : Matrix (Fin 2) (Fin 2) K).charpoly = (X - C a) * (X - C b) := by
  have e : ((g * r * g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      (r : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj g _
  rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => h i j hij), Fin.prod_univ_two, ← ha, ← hb]

theorem UpperTheory.V.Sd.eisReg :
    UpperTheory.V.Sd.EisReg := by
  intro l hl Ω _ _ _ ι φ θ k hk ρ hρ H hH
  obtain ⟨A, hA⟩ := eisReg_place (Ω := Ω) l hl.out
  obtain ⟨κ, ⟨g, hg⟩, hκ, -⟩ := hρ.above A hA
  obtain ⟨u, hu⟩ := GlobalTheory.CycDec.exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  haveI : IsGalois ℚ Ω := {}
  haveI : Finite (G ℚ Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hnH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := H) Subgroup.FiniteIndex.index_ne_zero σ
  have hs : σ ^ n ∈ Ine (F := ℚ) A := pow_mem hσ n
  let s : ↥(Dec (F := ℚ) A) := ⟨σ ^ n, Ine_le_Dec A hs⟩
  refine ⟨σ ^ n, hnH, cycBar ℚ Ω l (σ ^ n) ^ ((k : ℤ) - 1), ?_, ?_⟩
  · rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨m, hm, h⟩
    have hinj : Function.Injective
        (Units.map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom) :=
      Units.map_injective ((algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective)
    refine hu ((n : ℤ) * ((k : ℤ) - 1) * m) ?_ (hinj ?_)
    · have : (0 : ℤ) < (k : ℤ) - 1 := by omega
      positivity
    · rw [map_one, ← h, cycBar, MonoidHom.comp_apply, map_pow, hσu, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
        map_pow, map_zpow]
  · refine eisReg_charpoly g (ρ (σ ^ n)) _ _ (hg s).1 ?_ ?_
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 0, hκ 0 s hs]; rfl
    · rw [show ρ (σ ^ n) = ρ s from rfl, (hg s).2 1, hκ 1 s hs]; simp
end

section

open UpperTheory.V in
theorem UpperTheory.V.Sd.dirOf :
    UpperTheory.V.Sd.DirOf := by
  intro l _ Ω _ _ _ ι N hN φ hφ
  have : NeZero N := ⟨hN.ne'⟩
  have hs := (Chr.clsOnto Ω N).1
  have hk : (Chr.cls ℚ Ω N).ker ≤ φ.ker := fun s h => by
    have h1 : Chr.cls ℚ Ω N s = 1 := h
    refine hφ s fun ζ hζ => ?_
    rw [Chr.cls_spec N s ζ hζ, h1, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  let f := MonoidHom.liftOfRightInverse (Chr.cls ℚ Ω N) (Function.surjInv hs)
    (Function.rightInverse_surjInv hs) ⟨φ, hk⟩
  have hf : ∀ s, f (Chr.cls ℚ Ω N s) = φ s := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ, hk⟩ s
  let χ₀ : DirichletCharacter ℂ N := MulChar.ofUnitHom ((Units.map ι.toRingHom.toMonoidHom).comp f)
  have hd : χ₀.conductor ∣ N := χ₀.conductor_dvd_level
  have hM : NeZero χ₀.conductor := ⟨χ₀.conductor_ne_zero⟩
  refine ⟨χ₀.conductor, hM, χ₀.primitiveCharacter, hd, χ₀.primitiveCharacter_isPrimitive, ?_⟩
  ext s
  have h1 := DFunLike.congr_fun ((Chr.clsFacts ℚ Ω N).2.1 _ hd) s
  have h2 : χ₀.primitiveCharacter (ZMod.unitsMap hd (Chr.cls ℚ Ω N s)) = χ₀ (Chr.cls ℚ Ω N s) := by
    conv_rhs => rw [← χ₀.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
    simp [ZMod.unitsMap_def]
  have h3 : χ₀ (Chr.cls ℚ Ω N s) = ι (φ s) := by
    rw [← hf]
    simp [χ₀]
  rw [Chr.dirG, MonoidHom.comp_apply, ← h1, MulChar.coe_toUnitHom, MulChar.ringHomComp_apply, MonoidHom.comp_apply, h2, h3]
  simp
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem isIrr_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (r' : Γ' →* GL (Fin n) k) (h : ∀ g, ∃ g', r' g' = r g) (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W hW hi => h3 W hW fun g v hv => ?_⟩
  obtain ⟨g', e⟩ := h g
  rw [← e]
  exact hi g' v hv

theorem UpperTheory.V.Sd.resFacts :
    UpperTheory.V.Sd.ResFacts := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ l _ n r
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsAlgClosure F Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  obtain ⟨hemb, hopen, -⟩ := galEmbTop F E Ω
  have hoe : Topology.IsOpenEmbedding (galEmb F E Ω) := by
    refine ⟨hemb, ?_⟩
    rw [← MonoidHom.coe_range, range_galEmb]
    exact hopen
  have hcyc : (cycBar F Ω l).comp (galEmb F E Ω) = cycBar E Ω l := rfl
  have hD : ∀ (A : ValuationSubring Ω) (s : _root_.Formalism.ConjugateSelfDual.G E Ω), s ∈ _root_.ReciprocityTheory.Gal.Dec (F := E) A → galEmb F E Ω s ∈ _root_.ReciprocityTheory.Gal.Dec (F := F) A :=
    fun A s hs => hs
  have hI : ∀ (A : ValuationSubring Ω) (s : _root_.Formalism.ConjugateSelfDual.G E Ω), s ∈ Ine (F := E) A → galEmb F E Ω s ∈ Ine (F := F) A :=
    fun A s hs => ⟨hD A s hs.1, hs.2⟩
  refine ⟨hemb.continuous, hopen, hcyc, ⟨isIrr_of_range _ _ ?_, isIrr_of_range _ _ ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    rw [← range_galEmb] at hg
    obtain ⟨g', rfl⟩ := hg
    exact ⟨g', rfl⟩
  · exact fun g => ⟨⟨_, galEmb_mem F E Ω g⟩, rfl⟩
  · intro h H hH
    refine isIrr_of_range _ _ ?_ (h (H.map (galEmb F E Ω)) (hoe.isOpenMap _ hH))
    rintro ⟨g, g', hg', rfl⟩
    exact ⟨⟨g', hg'⟩, rfl⟩
  · intro τ h A hA
    obtain ⟨g, hg⟩ := h A hA
    exact ⟨g, fun s hs => hg _ (hI A s hs)⟩
  · rintro m ψ A ⟨κ, ⟨g, hg⟩, h2, h3⟩
    let j : ↥(_root_.ReciprocityTheory.Gal.Dec (F := E) A) →* ↥(_root_.ReciprocityTheory.Gal.Dec (F := F) A) :=
      ((galEmb F E Ω).comp (_root_.ReciprocityTheory.Gal.Dec (F := E) A).subtype).codRestrict _ fun s => hD A s s.2
    exact ⟨fun i => (κ i).comp j, ⟨g, fun s => hg (j s)⟩, fun i s hs => h2 i (j s) (hI A s hs), fun i s => h3 i (j s)⟩
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix Topology

namespace UpperTheory.V.Sd

private theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : GeneralLinearGroup.det (aff y x) = y := by
  ext
  simp [aff, Matrix.det_fin_two]

private theorem exists_sign (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (d : (TR.Rinf F)ˣ) :
    ∃ a : Fˣ, ∀ v, 0 < ((TR.pInf F).comp (algebraMap F (Ad F)) (a : F)) v * (d : TR.Rinf F) v := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  have hd : DenseRange ((TR.pInf F).comp (algebraMap F (Ad F))) :=
    (TR.infEq F).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) hc
  have ho : IsOpen {x : TR.Rinf F | ∀ v, 0 < x v * (d : TR.Rinf F) v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (by fun_prop)
  have hne : ∀ v, (d : TR.Rinf F) v ≠ 0 := fun v h => by
    have := congrFun d.mul_inv v
    simp [h] at this
  obtain ⟨a, ha⟩ := hd.exists_mem_open ho ⟨d, fun v => mul_self_pos.2 (hne v)⟩
  refine ⟨Units.mk0 a ?_, ha⟩
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa using ha v

private theorem exists_sl (F : Type) [Field F] [NumberField F] (K : Subgroup (GL (Fin 2) (Af F)))
    (hK : IsOpen (K : Set (GL (Fin 2) (Af F)))) (g : GL (Fin 2) (Af F)) :
    ∃ (σ : GL (Fin 2) F) (y : (Af F)ˣ) (u : GL (Fin 2) (Af F)), u ∈ K ∧ GeneralLinearGroup.det σ = 1 ∧
      g = GeneralLinearGroup.map (algebraMap F (Af F)) σ * (aff y 0 * u) := by
  set y := GeneralLinearGroup.det g with hy
  have hs : g * (aff y 0)⁻¹ ∈ GroundTheory.Automorphic.AdelicGLn.finiteSL F 2 := by
    rw [GroundTheory.Automorphic.AdelicGLn.mem_finiteSL, map_mul, map_inv, det_aff, hy, mul_inv_cancel]
  have hcl := GroundTheory.Automorphic.AdelicGLn.finiteSL_le_topologicalClosure F 2 hs
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hcl
  have ho : IsOpen {s : GL (Fin 2) (Af F) | (aff y 0)⁻¹ * s⁻¹ * g ∈ K} :=
    hK.preimage (f := fun s : GL (Fin 2) (Af F) => (aff y 0)⁻¹ * s⁻¹ * g) ((continuous_const.mul continuous_inv).mul continuous_const)
  obtain ⟨_, hu, σ, hσ, rfl⟩ := mem_closure_iff.1 hcl _ ho (by
    rw [Set.mem_setOf_eq, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_left, inv_mul_cancel]; exact one_mem K)
  refine ⟨σ, y, _, hu, hσ, ?_⟩
  rw [mul_assoc, mul_inv_cancel_left]
  exact (mul_inv_cancel_left _ g).symm

end UpperTheory.V.Sd

open UpperTheory.V UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.strongApp :
    UpperTheory.V.Sd.StrongApp := by
  intro F _ _ _ K hK g
  set j := (TR.pInf F).comp (algebraMap F (Ad F)) with hj
  set gi := GeneralLinearGroup.map (TR.pInf F) g with hgi
  obtain ⟨a, ha⟩ := exists_sign F (GeneralLinearGroup.det gi)
  obtain ⟨σ, y, u, hu, hσ, e⟩ := exists_sl F K hK
    ((GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0))⁻¹ * GeneralLinearGroup.map (pFin F) g)
  have hγ : GeneralLinearGroup.det (aff a 0 * σ) = a := by rw [map_mul, det_aff, hσ, mul_one]
  set h := (GeneralLinearGroup.map j (aff a 0 * σ))⁻¹ * gi with hh
  have hh' : GeneralLinearGroup.map j (aff a 0 * σ) * h = gi := by rw [hh, mul_inv_cancel_left]
  have e' : GeneralLinearGroup.map (algebraMap F (Af F)) (aff a 0 * σ) * (aff y 0 * u) =
      GeneralLinearGroup.map (pFin F) g := by
    rw [inv_mul_eq_iff_eq_mul.1 e, map_mul, mul_assoc]
  generalize aff a 0 * σ = γ at *
  refine ⟨γ, h, y, u, hu, fun v => ?_, TR.ga_ext ?_ ?_⟩
  · have h1 := ha v
    rw [← hh', map_mul, Units.val_mul, GlobalTheory.CuspRep.det_map, hγ, Pi.mul_apply, ← hj, ← mul_assoc] at h1
    exact (pos_iff_pos_of_mul_pos h1).1 (lt_of_le_of_ne (mul_self_nonneg _) fun h0 => by simp [← h0] at h1)
  · rw [map_mul, map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, ← hgi, ← hh']
    rfl
  · rw [map_mul, map_mul, TR.pFin_infGL, one_mul, ← e']
    congr 1
    simp
end
