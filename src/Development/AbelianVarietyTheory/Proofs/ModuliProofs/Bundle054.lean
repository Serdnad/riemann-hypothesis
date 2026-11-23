module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Flat.TorsionFree
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PeriodDatum

noncomputable section

lemma lattice_equiv {La : Type} [AddCommGroup La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧
      ∃ e : ℝ ⊗[ℤ] La ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, e (1 ⊗ₜ x) = P x := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  let f : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hinj
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ La := Module.Finite.equiv f.symm
  haveI : Module.Free ℤ La := Module.Free.of_equiv f.symm
  have hr : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [f.finrank_eq, ZLattice.rank ℝ L]
  have hg : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
  let φ : ℝ ⊗[ℤ] La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hφ : ∀ x, φ (1 ⊗ₜ x) = P x := fun x => by simp [φ]
  have hs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hφ x⟩
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] La) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_baseChange, hr]
  exact ⟨inferInstance, hr.trans hg, LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hs, hs⟩, hφ⟩

lemma hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

lemma hermForm_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = starRingEnd ℂ c * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

lemma hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

lemma hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add]

lemma hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    (hermForm Hm z z).im = 0 := by
  have := h.im_star_dotProduct_mulVec_self (star z)
  simpa [hermForm] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma two_mul_eq_of_isTypeFn (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty 1
  have h2 := PeriodNonempty.sum_type H he 1
  simp only [map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Embeddings.card, Nat.cast_one] at h1 h2
  have : (2 * g : ℂ) = Module.finrank ℚ E * (p + q) := by rw [h1, h2]; ring
  exact_mod_cast this

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ))
    (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF →
    (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) →
    ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y) := by
  intro E _ _ _ H La _ _ EF p q g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  classical
  obtain ⟨hfin, hrk, e, he⟩ := lattice_equiv P hinj hdisc hspan
  haveI : Module.Finite (𝓞 E) La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) La
  have htor : Submodule.torsion (𝓞 E) La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have ha0 : (a : E) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    rw [Submodule.mem_bot]
    apply hinj
    funext i
    have h1 := hlin a x i
    have h2 : a • x = 0 := hx
    rw [h2, map_zero] at h1
    rw [map_zero]
    exact (mul_eq_zero.1 h1.symm).resolve_left ((map_ne_zero (ty i)).2 ha0)
  haveI : Module.Flat (𝓞 E) La := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) La := Module.Flat.projective_of_finitePresentation
  have hrank : Module.finrank (𝓞 E) La = p + q := by
    have h1 := finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := La)
    rw [hrk, two_mul_eq_of_isTypeFn H hty, RingOfIntegers.rank] at h1
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1).symm
  have het : ∀ (r : ℝ) x, e (r ⊗ₜ x) = (r : ℂ) • P x := fun r x => by
    rw [← he, Complex.coe_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hB : ∀ x y, EF.baseChange ℝ x y = (hermForm Hm (e x) (e y)).im := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp [hermForm]
    | add x x' h h' => simp only [map_add (f := _), LinearMap.add_apply, h, h', hermForm_add_left, Complex.add_im]
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hermForm]
      | add y y' h h' => simp only [map_add (f := _), h, h', hermForm_add_right, Complex.add_im]
      | tmul r' y =>
        rw [het, het, hermForm_smul_left, hermForm_smul_right, LinearMap.BilinForm.baseChange_tmul]
        simp [him]
        ring
  let d : (Fin g → ℂ) → Module.End ℂ (Fin g → ℂ) := fun c => Matrix.toLin' (Matrix.diagonal c)
  have hd : ∀ c z i, d c z i = c i * z i := fun c z i => by simp [d, Matrix.mulVec_diagonal]
  have hdt : ∀ c, LinearMap.trace ℝ _ (e.symm.conj ((d c).restrictScalars ℝ)) = 2 * (∑ i, c i).re := fun c => by
    rw [LinearMap.trace_conj', PeriodNonempty.trace_real]
    simp [d]
  let J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La := e.symm.conj ((d fun _ => Complex.I).restrictScalars ℝ)
  have hJ : ∀ x, e (J x) = Complex.I • e x := fun x => by
    funext i
    simp [J, LinearEquiv.conj_apply, hd]
  refine ⟨{ La := La, fin := inferInstance, proj := hproj, EF := EF, alt := fun x => ?_, unimod := hbij,
            adj := hadj, p := p, q := q, rank := hrank, dom := ⟨J, fun x => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩ },
    LinearEquiv.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  · have := him x x
    rw [hermForm_self_im hH] at this
    exact_mod_cast this.symm
  · apply e.injective
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · rw [hB, hB, hJ, hJ, hermForm_smul_left, hermForm_smul_right]
    simp
  · rw [hB, hJ, hermForm_smul_left]
    simpa using hpos (e x) (by simpa using hx)
  · intro a A t hA ht
    rw [← PeriodNonempty.sum_type H hty] at ht
    have hAe : ∀ x i, e (A x) i = ty i (a : E) * e x i := fun x i => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add (f := _), Pi.add_apply, h, h', mul_add]
      | tmul r x =>
        have : (r ⊗ₜ[ℤ] x : ℝ ⊗[ℤ] La) = r • (1 ⊗ₜ[ℤ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hA, map_smul, map_smul, he, he]
        simp only [Pi.smul_apply, hlin, Complex.real_smul]
        ring
    have h1 : A = e.symm.conj ((d fun i => ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe]
    have h2 : J ∘ₗ A = e.symm.conj ((d fun i => Complex.I * ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe, hJ, mul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp only [LinearMap.comp_apply, hJ, hAe, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [h1, hdt, ht]
    · rw [h2, hdt, ht, ← Finset.mul_sum]
      simp

end

end GlobalTheory.PeriodDatum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.exists_finite_etale_surjective_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l₁ : Level H), l₀.Dvd l₁ → ∃ (k : KA l₀ →+* KA l₁) (r : (Xo l₁).X ⟶ (Xo l₀).X) (ν : SABMap (Xo l₁).univ.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = (Xo l₁).s ≫ spMap k), IsInc (KA l₀).val.toRingHom (KA l₁).val.toRingHom k ∧ LevComp (Xo l₁).univ (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) ∧ IsFinite r ∧ Etale r ∧ Surjective r := by
  first | exact @GlobalTheory.LevelMap.exists_levelMap | exact GlobalTheory.LevelMap.exists_levelMap | (intros; apply GlobalTheory.LevelMap.exists_levelMap <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevelMapField

private theorem KA_mono_of_A_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.A ∣ l.A) : KA l₀ ≤ KA l := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [GlobalTheory.LevelCover.zeta_dvd l.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

private theorem M'_dvd_of_level_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.Dvd l) : l₀.M' ∣ l.M' := by
  unfold Level.Dvd at h
  unfold Level.M'
  exact Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))

private theorem M'_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Level H) : 0 < l.M' := by
  unfold Level.M'
  have h3 := l.three_le
  exact Nat.lcm_pos (by omega) l.A_pos

theorem exists_levelMap : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)) (_ : ObjMap o (Xo l).univ (pullback.fst _ _)), l₀.Dvd l → ∃ (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap o.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k), IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp o (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  intro _ _ _ E _ _ _ H D Xo hN l₀ l c o mo hd
  have hA : l₀.A ∣ l.A := by
    unfold Level.Dvd at hd
    exact hd.2.2
  have hle : KA l₀ ≤ c.F := (KA_mono_of_A_dvd hA).trans c.le
  have hz : zeta l₀.M' ∈ c.F := by
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos' l) (M'_dvd_of_level_dvd hd)]
    exact pow_mem c.zeta_mem _
  obtain ⟨r₀, -, m, -, -, hm1, hm2, -, hF⟩ := hN l₀ l (Xo l₀) (Xo l) hd
  obtain ⟨rF, h1, h2, hfin, het, hsurj, -⟩ := hF ⟨c.F, c.fin, c.conj, hz, hle⟩ c rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c.F)).toRingHom = 𝟙 (Sp c.F) :=
    GlobalTheory.LevelCover.spMap_inclusion_self _
  have hr : (rF ≫ pullback.fst _ _) ≫ (Xo l₀).s =
      pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
    erw [hid, Category.comp_id]
  have hlift : pullback.lift (rF ≫ pullback.fst _ _) (pullback.snd _ _) hr = rF := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, h2]
      erw [hid, Category.comp_id]
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelCover.sab_comp mo.toSABMap m (e := rF ≫ pullback.fst _ _) h1.symm
  refine ⟨(IntermediateField.inclusion hle).toRingHom, rF ≫ pullback.fst _ _, ν, hr,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · unfold LevComp
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.eta a) ((Xo l).univ.eta a) (mo.eta a),
        Category.assoc, hm1 a, ← Category.assoc, ← h1]
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.etaA a) ((Xo l).univ.etaA a) (mo.etaA a),
        Category.assoc, hm2 a, ← Category.assoc, ← h1]
  · rw [hlift]; exact hfin
  · rw [hlift]; exact het
  · rw [hlift]; exact hsurj

end GlobalTheory.LevelMapField
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.Proof.TautologicalModel

section Taut

variable {X X' Y Z : Scheme.{0}}

theorem taut_le (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (J : PUnit → L.ι) (K : PUnit → PUnit → L.ι) :
    (L.pull (p ≫ F)).U J ⊓ ((L.pull F).pull p).U K ≤ (p ≫ F) ⁻¹ᵁ (L.U (J ⟨⟩) ⊓ L.U (K ⟨⟩ ⟨⟩)) := fun _ hy =>
  ⟨mem_pull.1 hy.1, mem_pull (L := L) (F := F).1 (mem_pull (L := L.pull F) (F := p).1 hy.2)⟩

def taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') : LB.Iso ((L.pull F).pull p) (L.pull (p ≫ F)) :=
  ⟨fun q => res (taut_le L F p q.1 q.2) (pullU (p ≫ F) _ (L.g (q.1 ⟨⟩) (q.2 ⟨⟩ ⟨⟩)))⟩

theorem gw_taut (L : LB X) (F : X' ⟶ X) (p : Y ⟶ X') (f : Z ⟶ Y) (z : Z) (j : L.ι) (k : PUnit → PUnit → L.ι)
    (hj : (p ≫ F) (f z) ∈ L.U j) (hk : f z ∈ ((L.pull F).pull p).U k) :
    gw (taut L F p) f z j k = gm (f ≫ p ≫ F) z _ (L.g j (k ⟨⟩ ⟨⟩)) := by
  have hm : f z ∈ (L.pull (p ≫ F)).U (fun _ => j) ⊓ ((L.pull F).pull p).U k := ⟨mem_pull.2 hj, hk⟩
  exact (gm_res f z (taut_le L F p _ k) hm _).trans (gm_pull f (p ≫ F) z _ (taut_le L F p _ k hm) _)

theorem taut_isGen {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (p : Y ⟶ X') : (taut L F p).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have h1 : (f ≫ p) z ∈ (L.pull F).U (k ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk
  have h1' : (f ≫ p) z ∈ (L.pull F).U (k' ⟨⟩) := mem_pull (L := L.pull F) (F := p).1 hk'
  have h2 : (f ≫ p ≫ F) z ∈ L.U (k ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1
  have h2' : (f ≫ p ≫ F) z ∈ L.U (k' ⟨⟩ ⟨⟩) := mem_pull (L := L) (F := F).1 h1'
  rw [gw_taut L F p f z j k hj hk, gw_taut L F p f z j' k' hj' hk', gm_pull_g (L.pull F) p f z k k' hk hk',
    gm_pull_g L F (f ≫ p) z _ _ h1 h1', Category.assoc,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j) (j := j') hj hj' h2,
    ← gm_cocycle hL (f ≫ p ≫ F) z (i := j') (j := k ⟨⟩ ⟨⟩) hj' h2 h2']
  generalize gm (f ≫ p ≫ F) z _ (L.g j j') = A
  generalize gm (f ≫ p ≫ F) z _ (L.g j' (k ⟨⟩ ⟨⟩)) = B
  generalize gm (f ≫ p ≫ F) z _ (L.g (k ⟨⟩ ⟨⟩) (k' ⟨⟩ ⟨⟩)) = C
  rw [_root_.mul_comm B C, _root_.mul_assoc, inv_mul_cancel_left]

end Taut

section Rig

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem gm_rigPullOf (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) {Z : Scheme.{0}}
    (f : Z ⟶ (𝟙_ (Over S')).left) (z : Z) (j : PUnit → PUnit → L.ι)
    (hj : f z ∈ LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) :
    gm f z (LB.wchart (L.pull F) (fun _ : PUnit => eSec G') j) ((rigPullOf F e he L r).s j) =
      gm (f ≫ e) z (LB.wchart L (fun _ : PUnit => eSec G) (fun _ => j ⟨⟩ ⟨⟩)) (r.s (fun _ => j ⟨⟩ ⟨⟩)) :=
  (gm_res f z (rigPull_le F e he L j) hj _).trans (gm_pull f e z _ (rigPull_le F e he L j hj) _)

theorem rigPullOf_isGen (F : G'.left ⟶ G.left) (e : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left)
    (he : eSec G' ≫ F = e ≫ eSec G) (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) :
    (rigPullOf F e he L r).IsGen := by
  intro i j
  refine unit_ext fun y hy => ?_
  have hi' := rigPull_le F e he L i hy.1
  have hj' := rigPull_le F e he L j hy.2
  refine ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y i hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g (L.pull F) (eSec G') (𝟙 _) y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (gm_rigPullOf F e he L r (𝟙 _) y j hy.2)))).trans ?_
  rw [gen_trans (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) hr (𝟙 _ ≫ e) y hi' hj', trF, Fintype.prod_unique,
    zpow_one, gm_pull_g L F (𝟙 _ ≫ eSec G') y (i ⟨⟩) (j ⟨⟩) (mem_pull (L := L.pull F) (F := eSec G').1 hy.1)
      (mem_pull (L := L.pull F) (F := eSec G').1 hy.2), Category.assoc, Category.assoc, he]

end Rig

end GlobalTheory.Proof.TautologicalModel
end
end
