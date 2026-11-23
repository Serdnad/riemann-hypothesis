module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem primRam_lift (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (r : ℕ) (hr : r.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (r : Ω) < 1) (u : (ZMod N)ˣ)
    (hu : u ∈ (ZMod.unitsMap (Nat.ordCompl_dvd N r)).ker) :
    ∃ σ ∈ Ine (F := ℚ) A, Chr.cls ℚ Ω N σ = u := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨v, hv⟩ := KStar.TotallyRealRoots.redPow_surjective (l := r) (N.factorization r)
    (ZMod.unitsMap (Nat.ordProj_dvd N r) u)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω r A hA v
  refine ⟨σ, hσ, ?_⟩
  apply (Chr.clsFacts ℚ Ω N).2.2.1
  refine (LDataCardLeFinrank.classIff Ω r N σ.toRingEquiv u).2 ⟨?_, ?_⟩
  · intro ζ hζ
    have hcop : (N / r ^ N.factorization r).Coprime r :=
      (Nat.coprime_ordCompl hr (NeZero.ne N)).symm
    have hfix := (LDataCardLeFinrank.ineFixRoots ℚ Ω r A hA (N / r ^ N.factorization r) hcop ζ hζ).2 σ hσ
    rw [MonoidHom.mem_ker.mp hu, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ,
      pow_one]
    exact hfix
  · rw [← hv, ← hσv]
    rfl

private theorem primRam_l (l : ℕ) [Fact l.Prime] (c : HV.Coef l) : ¬ IsUnit (l : c.O) := by
  intro hu
  haveI := c.fin
  haveI : Algebra.IsIntegral ℤ_[l] c.O := Algebra.IsIntegral.of_finite ℤ_[l] c.O
  have hker : RingHom.ker (algebraMap ℤ_[l] c.O) ≤ IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  obtain ⟨Q, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (IsLocalRing.maximalIdeal ℤ_[l]) hker
  have hl : ((l : ℤ_[l])) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [← hQc, Ideal.mem_comap, map_natCast] at hl
  exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hl hu)

private theorem primRam_unit (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (n : ℕ) (hn : ¬ l ∣ n) (x : c.O) (hx : x ^ n = 1)
    (h1 : x ≠ 1) : IsUnit (x - 1) := by
  haveI := c.dvr
  by_contra hne
  have hm : x - 1 ∈ IsLocalRing.maximalIdeal c.O := (IsLocalRing.mem_maximalIdeal _).2 hne
  have hsum : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    have h := mul_geom_sum x n
    rw [hx, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr h1)
  have hdiff : ∑ i ∈ Finset.range n, (x ^ i - 1) ∈ IsLocalRing.maximalIdeal c.O := by
    refine Ideal.sum_mem _ fun i _ => ?_
    obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow x 1 i
    rw [one_pow] at hy
    rw [hy]
    exact Ideal.mul_mem_right _ _ hm
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  have hlm : (l : c.O) ∈ IsLocalRing.maximalIdeal c.O :=
    (IsLocalRing.mem_maximalIdeal _).2 (primRam_l l c)
  have hcop : IsCoprime ((l : ℤ)) (n : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 hn)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom c.O)
  simp only [eq_intCast, Int.cast_natCast] at hab
  have h1m : (1 : c.O) ∈ IsLocalRing.maximalIdeal c.O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hdiff)
  exact (IsLocalRing.maximalIdeal.isMaximal c.O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)

private theorem exists_prime_dvd_over_of_over_mul_iff (Ω : Type) [Field Ω] (A : ValuationSubring Ω)
    (hmul : ∀ m n : ℕ, Over A (m * n) ↔ Over A m ∨ Over A n) (n : ℕ) (hn : n ≠ 0) (h : Over A n) :
    ∃ r, r.Prime ∧ r ∣ n ∧ Over A r := by
  refine Nat.recOnMul (motive := fun n => n ≠ 0 → Over A n → ∃ r, r.Prime ∧ r ∣ n ∧ Over A r)
    ?_ ?_ ?_ ?_ n hn h
  · intro h0
    exact absurd rfl h0
  · intro _ h1
    simp [Over] at h1
  · intro p hp _ hpA
    exact ⟨p, hp, dvd_rfl, hpA⟩
  · intro a b iha ihb hab hAab
    rcases (hmul a b).1 hAab with ha | hb
    · obtain ⟨r, hr, hra, hrA⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨r, hr, hra.mul_right b, hrA⟩
    · obtain ⟨r, hr, hrb, hrA⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨r, hr, hrb.mul_left a, hrA⟩

theorem UpperTheory.V.ML.primRam :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (f : ℕ) [NeZero f] (ψ : DirichletCharacter c.O f), ψ.IsPrimitive → ¬ l ∣ orderOf ψ →
    (∀ A : ValuationSubring Ω, Over A f → ∃ g ∈ Ine (F := ℚ) A, IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1)) ∧
    (∀ A : ValuationSubring Ω, ¬ Over A f → ∀ g ∈ Ine (F := ℚ) A, Chr.dirG ℚ Ω ψ g = 1) ∧ ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 → IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
  intro Ω _ inst _ l _ c f _ ψ hprim hord
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hpb := placeBasic Ω
  have hC : ∀ g : G ℚ Ω, Chr.dirG ℚ Ω ψ g ≠ 1 →
      IsUnit (((Chr.dirG ℚ Ω ψ g : c.Oˣ) : c.O) - 1) := by
    intro g hg
    apply primRam_unit l c (orderOf ψ) hord
    · show ((MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) : c.Oˣ) : c.O) ^ orderOf ψ = 1
      rw [MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply_coe]
    · intro h
      exact hg (Units.val_eq_one.mp h)
  refine ⟨?_, ?_, hC⟩
  · intro A hA
    obtain ⟨r, hr, hrf, hAr⟩ := exists_prime_dvd_over_of_over_mul_iff Ω A (hpb.2.2.1 A) f (NeZero.ne f) hA
    have hsub : ¬ (ZMod.unitsMap (Nat.ordCompl_dvd f r)).ker ≤ (MulChar.toUnitHom ψ).ker := by
      intro hle
      have hft := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ψ)
        (Nat.ordCompl_dvd f r)).2 hle
      have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hft
      rw [(DirichletCharacter.isPrimitive_def ψ).1 hprim] at hdvd
      have hpos : 0 < f / r ^ f.factorization r := Nat.ordCompl_pos r (NeZero.ne f)
      have hlt : f / r ^ f.factorization r < f :=
        Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne f))
          (Nat.one_lt_pow (hr.factorization_pos_of_dvd (NeZero.ne f) hrf).ne' hr.one_lt)
      exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hlt)
    obtain ⟨u, hu, hψu⟩ := SetLike.not_le_iff_exists.mp hsub
    obtain ⟨σ, hσ, hσu⟩ := primRam_lift Ω f r hr A hAr u hu
    refine ⟨σ, hσ, hC σ ?_⟩
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f σ) ≠ 1
    rw [hσu]
    exact fun h => hψu (MonoidHom.mem_ker.mpr h)
  · intro A hA g hg
    have hk := (Chr.clsFacts ℚ Ω f).2.2.2.2 A hA hg
    show MulChar.toUnitHom ψ (Chr.cls ℚ Ω f g) = 1
    rw [MonoidHom.mem_ker.mp hk, map_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem opP_mul' (δ : G ℚ Ω) (a : ℕ) (x y : Ω) : opP δ a (x * y) = opP δ a x * opP δ a y := by
  simp only [opP, map_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

private theorem opP_ne' (δ : G ℚ Ω) (a : ℕ) {x : Ω} (hx : x ≠ 0) : opP δ a x ≠ 0 :=
  div_ne_zero ((map_ne_zero δ).2 hx) (pow_ne_zero _ hx)

private theorem opP_eq' {M a : ℕ} (hM : M ≠ 0) {δ : G ℚ Ω} (hδ : Pows M a δ) {x y : Ω} (hy : y ^ M ≠ 0)
    (h : x ^ M = y ^ M) : opP δ a x = opP δ a y := by
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hy
    exact hy rfl
  have hw : (x / y) ^ M = 1 := by rw [div_pow, h, div_self hy]
  have hw0 : x / y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hw
    exact zero_ne_one hw
  have hx : x = y * (x / y) := (mul_div_cancel₀ x hy0).symm
  have h1 : opP δ a (x / y) = 1 := by
    unfold opP
    rw [hδ _ hw, div_self (pow_ne_zero _ hw0)]
  rw [hx, opP_mul', h1, mul_one]

private theorem zeta_inj' {M : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) {i j k : ZMod M}
    (h : ζ ^ i.val = ζ ^ j.val * ζ ^ k.val) : i = j + k := by
  rw [← pow_add] at h
  have h2 : ζ ^ (j.val + k.val) = ζ ^ ((j + k).val) := by
    rw [ZMod.val_add]
    conv_lhs => rw [← Nat.mod_add_div (j.val + k.val) M, pow_add, pow_mul, hζ.pow_eq_one,
      one_pow, mul_one]
  exact ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h.trans h2))

end

theorem UpperTheory.V.ML.kolHom :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → M ∣ F → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    ∀ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ →
    (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) ∧ IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) ∧
    ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y → ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
  intro Ω _ _ _ M F n a _ hFn hMF ζ hζ δ hδ y hy hfix κ hK
  have hM : M ≠ 0 := NeZero.ne M
  have gb := galBasic Ω (F * n) hFn
  have gbF : fixMu ℚ Ω (F * n) ≤ fixMu ℚ Ω F := gb.2.2.2.2.2.2.2.2.1 F (dvd_mul_right F n)
  obtain ⟨Y₀, hY₀, hK'⟩ := hK
  have hgy : ∀ g : G ℚ Ω, g y / y ≠ 0 := fun g => div_ne_zero ((map_ne_zero g).mpr hy) hy
  have hY0 : Y₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM] at hY₀
    exact hy hY₀.symm
  have hA : opP δ a Y₀ ≠ 0 := opP_ne' δ a hY0
  have key : ∀ Y : Ω, Y ^ M = y → ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro Y hY g hg z hz
    obtain ⟨z₀, -, hz₀, hκ⟩ := hK' g hg
    have e1 : opP δ a Y = opP δ a Y₀ :=
      opP_eq' hM hδ (by rw [hY₀]; exact hy) (hY.trans hY₀.symm)
    have e2 : opP δ a z = opP δ a z₀ :=
      opP_eq' hM hδ (by rw [hz₀]; exact hgy g) (hz.trans hz₀.symm)
    rw [e1, e2]
    exact hκ
  have hmul : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v := by
    intro u hu v hv
    obtain ⟨zu, -, hzu, hκu⟩ := hK' u hu
    obtain ⟨zv, hzvfix, hzv, hκv⟩ := hK' v hv
    have hzu0 : zu ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzu
      exact hgy u hzu.symm
    have hzv0 : zv ≠ 0 := by
      intro h0
      rw [h0, zero_pow hM] at hzv
      exact hgy v hzv.symm
    have huy : u y ≠ 0 := (map_ne_zero u).mpr hy
    have hz : (u zv * zu) ^ M = (u * v) y / y := by
      rw [mul_pow, ← map_pow, hzv, hzu, map_div₀, AlgEquiv.mul_apply]
      field_simp
    have euv := key Y₀ hY₀ (u * v) (mul_mem hu hv) (u zv * zu) hz
    have hcomm : δ (u zv) = u (δ zv) := gb.2.2.2.2.2.1 zv hzvfix δ u
    have hPu : opP δ a (u zv) = u (opP δ a zv) := by
      unfold opP
      rw [hcomm, map_div₀, map_pow]
    rw [opP_mul', hPu, AlgEquiv.mul_apply] at euv
    have hfixζ : u (ζ ^ (κ v).val) = ζ ^ (κ v).val := by
      apply hu
      obtain ⟨c, hc⟩ := hMF
      rw [hc, pow_mul, ← pow_mul ζ, mul_comm (κ v).val M, pow_mul, hζ.pow_eq_one, one_pow,
        one_pow]
    have ev' : ζ ^ (κ v).val = u (v (opP δ a Y₀)) / u (opP δ a Y₀) / u (opP δ a zv) := by
      rw [← hfixζ, hκv, map_div₀, map_div₀]
    have hB : opP δ a zu ≠ 0 := opP_ne' δ a hzu0
    have huA : u (opP δ a Y₀) ≠ 0 := (map_ne_zero u).mpr hA
    have huC : u (opP δ a zv) ≠ 0 := (map_ne_zero u).mpr (opP_ne' δ a hzv0)
    apply zeta_inj' hζ
    rw [euv, hκu, ev']
    field_simp
  refine ⟨hmul, ?_, key⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral ℚ (opP δ a Y₀) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  haveI := IntermediateField.adjoin.finiteDimensional hint
  let H : Set (G ℚ Ω) := (fixMu ℚ Ω (F * n) : Set (G ℚ Ω)) ∩
    ((IntermediateField.adjoin ℚ {opP δ a Y₀}).fixingSubgroup : Set (G ℚ Ω))
  have hHo : IsOpen H := gb.2.1.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hH0 : ∀ h ∈ H, κ h = 0 := by
    rintro h ⟨h1, h2⟩
    have e := key Y₀ hY₀ h (gbF h1) 1 (by rw [one_pow, hfix h h1, div_self hy])
    have hP1 : opP δ a (1 : Ω) = 1 := by simp [opP]
    have hfx : h (opP δ a Y₀) = opP δ a Y₀ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp h2 _
        (IntermediateField.mem_adjoin_simple_self ℚ _)
    rw [hP1, hfx, div_self hA, div_one] at e
    have e0 := zeta_inj' hζ (i := κ h) (j := 0) (k := 0)
      (by rw [e, ZMod.val_zero, pow_zero, one_mul])
    simpa using e0
  have hS : IsOpen {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} :=
    hHo.preimage (continuous_const.mul continuous_subtype_val)
  have hx : x ∈ {w : fixMu ℚ Ω F | (x : G ℚ Ω)⁻¹ * w ∈ H} := by
    show (x : G ℚ Ω)⁻¹ * x ∈ H
    rw [inv_mul_cancel]
    exact ⟨one_mem _, one_mem _⟩
  filter_upwards [hS.mem_nhds hx] with w hw
  have hw' : (x : G ℚ Ω)⁻¹ * w ∈ fixMu ℚ Ω F := gbF hw.1
  have e := hmul x x.2 _ hw'
  rw [mul_inv_cancel_left, hH0 _ hw, add_zero] at e
  exact e
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.kolEx :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M F n a : ℕ) [NeZero M], F * n ≠ 0 → ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ δ : G ℚ Ω, Pows M a δ → ∀ y : Ω, y ≠ 0 → (∀ h ∈ fixMu ℚ Ω (F * n), h y = y) →
    (∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y) → ∃ κ : G ℚ Ω → ZMod M, IsKol M F n ζ δ a y κ := by
  intro Ω _ _ _ M F n a _ hFn ζ hζ δ hδ y hy hfix hz
  have hM : M ≠ 0 := NeZero.ne M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨Y, hY⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.pos_of_ne_zero hM)
  have hcomm := (galBasic Ω (F * n) hFn).2.2.2.2.2.1 y hfix
  have hroot : ∀ g ∈ fixMu ℚ Ω F, ∀ z : Ω, z ^ M = g y / y →
      ∃ k : ℕ, k < M ∧ ζ ^ k = g (opP δ a Y) / opP δ a Y / opP δ a z := by
    intro g _ z hz'
    apply hζ.eq_pow_of_pow_eq_one
    have hgy : g y ≠ 0 := by simpa using hy
    have hdy : δ y ≠ 0 := by simpa using hy
    have hdgy : δ (g y) ≠ 0 := by simpa using hgy
    unfold opP
    calc (g (δ Y / Y ^ a) / (δ Y / Y ^ a) / (δ z / z ^ a)) ^ M
        = g (δ (Y ^ M)) / (g (Y ^ M)) ^ a / (δ (Y ^ M) / (Y ^ M) ^ a) / (δ (z ^ M) / (z ^ M) ^ a) := by
          simp only [map_div₀, map_pow, div_pow]
          ring
      _ = 1 := by
          rw [hY, hz', map_div₀ δ, hcomm g δ]
          field_simp
          rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero a hy)]
  classical
  choose! zf hzf using hz
  have hk := fun g hg => hroot g hg (zf g) (hzf g hg).2
  choose! kf hkf using hk
  refine ⟨fun g => (kf g : ZMod M), Y, hY, fun g hg => ⟨zf g, (hzf g hg).1, (hzf g hg).2, ?_⟩⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hkf g hg).1]
  exact (hkf g hg).2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem val_add_smul {W : Type} [AddCommGroup W] {M : ℕ} [NeZero M] (x : W) (hx : M • x = 0) (a b : ZMod M) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← add_smul]
  conv_rhs => rw [← Nat.mod_add_div' (a.val + b.val) M]
  rw [add_smul, mul_smul, hx, smul_zero, add_zero]

private theorem lc_sum {X ι W : Type} [TopologicalSpace X] [AddCommGroup W] (s : Finset ι) (f : ι → X → W)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact IsLocallyConstant.const (0 : W)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

theorem UpperTheory.V.ML.nuIs :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (O W : Type) [CommRing O] [AddCommGroup W] [Module O W] (M F n : ℕ) [NeZero M] [NeZero F], F ∣ n → ∀ (β : G ℚ Ω →* Oˣ), (∀ g ∈ fixMu ℚ Ω F, (M : O) ∣ (β g : O) - 1) → ∀ σ : (ZMod F)ˣ → G ℚ Ω, (∀ t, Lifts F t (σ t)) →
    ∀ w : W, M • w = 0 → ∀ κ : G ℚ Ω → ZMod M, (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, κ (u * v) = κ u + κ v) → IsLocallyConstant (fun u : fixMu ℚ Ω F => κ u) →
    (∀ A : ValuationSubring Ω, ¬ Over A n → ∀ g ∈ Ine (F := ℚ) A, κ g = 0) → IsNu M F n β (nu β σ w κ) := by
  intro Ω _ _ _ O W _ _ _ M F n _ _ hFn β hβ σ hσ w hw κ hκ hlc hunr
  have hF0 : F ≠ 0 := NeZero.ne F
  obtain ⟨hN, -, -, -, hlift, -, -, -, -, hmul⟩ := galBasic Ω F hF0
  have pb := (placeBasic Ω).2.2.2.2.2.2.2.2.2
  have hcm : ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, g⁻¹ * u * g ∈ fixMu ℚ Ω F := by
    intro g u hu
    have := hN.conj_mem u hu g⁻¹
    rwa [inv_inv] at this
  have hfix : ∀ k ∈ fixMu ℚ Ω F, ∀ x : W, M • x = 0 → (β k : O) • x = x := by
    intro k hk x hx
    obtain ⟨c, hc⟩ := hβ k hk
    have e : (β k : O) = 1 + c * M := by
      rw [mul_comm, ← hc]
      ring
    rw [e, add_smul, one_smul, mul_smul, Nat.cast_smul_eq_nsmul, hx, smul_zero, add_zero]
  have hx : ∀ g : G ℚ Ω, M • ((β g : O) • w) = 0 := by
    intro g
    rw [smul_comm, hw, smul_zero]
  have h1 : κ 1 = 0 := by
    have := hκ 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    linear_combination -this
  have hinv : ∀ k ∈ fixMu ℚ Ω F, κ k⁻¹ + κ k = 0 := by
    intro k hk
    rw [← hκ _ (inv_mem hk) _ hk, inv_mul_cancel, h1]
  have hconj : ∀ k ∈ fixMu ℚ Ω F, ∀ y ∈ fixMu ℚ Ω F, κ (k⁻¹ * y * k) = κ y := by
    intro k hk y hy
    rw [hκ _ (mul_mem (inv_mem hk) hy) _ hk, hκ _ (inv_mem hk) _ hy]
    linear_combination hinv k hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    simp only [nu]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have e : (σ t)⁻¹ * (u * v) * σ t = ((σ t)⁻¹ * u * σ t) * ((σ t)⁻¹ * v * σ t) := by group
    rw [e, hκ _ (hcm _ u hu) _ (hcm _ v hv)]
    exact val_add_smul _ (hx (σ t)) _ _
  · simp only [nu]
    apply lc_sum
    intro t
    let c : fixMu ℚ Ω F → fixMu ℚ Ω F := fun u => ⟨(σ t)⁻¹ * u * σ t, hcm _ u u.2⟩
    have hc : Continuous c :=
      Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
    exact (hlc.comp_continuous hc).comp (fun k : ZMod M => k.val • ((β (σ t) : O) • w))
  · intro g u hu
    obtain ⟨b, hb⟩ := hlift g
    simp only [nu]
    rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft b)
      (fun t => (κ ((σ t)⁻¹ * (g * u * g⁻¹) * σ t)).val • (β (σ t) : O) • w)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    show (κ ((σ (b * s))⁻¹ * (g * u * g⁻¹) * σ (b * s))).val • (β (σ (b * s)) : O) • w = _
    have hk0 : (g * σ s)⁻¹ * σ (b * s) ∈ fixMu ℚ Ω F :=
      (hmul (b * s) (b * s) (g * σ s) (σ (b * s)) (hmul b s g (σ s) hb (hσ s)).1 (hσ (b * s))).2.2.mp rfl
    obtain ⟨k, hk, hτ⟩ : ∃ k ∈ fixMu ℚ Ω F, σ (b * s) = g * σ s * k := ⟨_, hk0, by group⟩
    rw [hτ]
    have e : (g * σ s * k)⁻¹ * (g * u * g⁻¹) * (g * σ s * k) = k⁻¹ * ((σ s)⁻¹ * u * σ s) * k := by group
    rw [e, hconj k hk _ (hcm _ u hu), map_mul, map_mul, Units.val_mul, Units.val_mul, mul_smul, mul_smul,
      hfix k hk w hw]
    exact smul_comm _ _ _
  · intro u hu
    simp only [nu]
    rw [Finset.smul_sum]
    apply Finset.sum_eq_zero
    intro t _
    rw [smul_comm, hx (σ t), smul_zero]
  · intro A hA g hg
    simp only [nu]
    apply Finset.sum_eq_zero
    intro t _
    have hA' : ¬ Over ((σ t)⁻¹ • A) n := by
      intro h'
      apply hA
      have := ((pb A (σ t)⁻¹).2.2.2.1 (n : Ω)).1
      rw [map_natCast] at this
      exact this h'
    have hmem : (σ t)⁻¹ * g * σ t ∈ Ine (F := ℚ) ((σ t)⁻¹ • A) := by
      rw [(pb A (σ t)⁻¹).2.1]
      have e : (σ t)⁻¹⁻¹ * ((σ t)⁻¹ * g * σ t) * (σ t)⁻¹ = g := by group
      rw [e]
      exact hg
    rw [hunr _ hA' _ hmem, ZMod.val_zero, zero_smul]
end
