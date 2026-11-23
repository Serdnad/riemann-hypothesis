module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle030
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.StTri

theorem descend {E R : Type} [Field E] [CommRing R] [Nontrivial R] (ι : E →+* R) {n m : ℕ}
    (w : Fin m → Fin n → E) (s : Set (Fin m)) (v : Fin n → E)
    (h : (fun i => ι (v i)) ∈ Submodule.span R ((fun a i => ι (w a i)) '' s)) :
    v ∈ Submodule.span E (w '' s) := by
  letI : Algebra E R := ι.toAlgebra
  have hinj : Function.Injective (Algebra.linearMap E R) := ι.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E R)
    (LinearMap.ker_eq_bot.mpr hinj)
  have hg1 : ∀ c : E, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  have hgm : ∀ (a : R) (c : E), g (a * ι c) = c * g a := by
    intro a c
    have : a * ι c = c • a := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul]
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, hv⟩ := h
  rw [Finsupp.mem_span_image_iff_linearCombination]
  refine ⟨Finsupp.mapRange g (map_zero g) l, ?_, ?_⟩
  · rw [Finsupp.mem_supported'] at hl ⊢
    intro i hi
    simp [hl i hi]
  · funext k
    have hk := congrFun hv k
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hk ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢

    rw [← hg1 (v k), ← hk, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hgm, Finsupp.mapRange_apply, mul_comm]

theorem hf_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : E) :
    hf L Hm x (c • y) = L.cj c * hf L Hm x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_add_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y z : Fin n → E) :
    hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem loc_step {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V)
    (hg : ∀ b : Fin (r + 1), (b : ℕ) < r → hf L S.Hm (g (Fin.last r)) (g b) = 0)
    (x : S.GLV) (hx : x ∈ S.Nof g) (j : Fin (r + 1)) : x (g j) - g j ∈ S.spanTo g j := by
  unfold Frames.Nof at hx
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_iInf] at hx
  obtain ⟨⟨_, hU⟩, hP⟩ := hx
  by_cases hj : (j : ℕ) < r
  · have h1 := (hU ⟨j, hj⟩).2 (g j) (Submodule.subset_span ⟨j, by simp, rfl⟩)
    simpa using h1
  · have hjr : (j : ℕ) = r := by omega
    have hjl : j = Fin.last r := Fin.ext hjr
    have hmem : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨b, hb, rfl⟩ := hy
        exact hg b hb
      | zero => simp [hf]
      | add y z _ _ hy hz => rw [hf_add_right, hy, hz, add_zero]
      | smul c y _ hy => rw [hf_smul_right, hy, mul_zero]
    have h2 := hP.2 _ hmem
    rw [hjl]
    simpa [Frames.spanTo] using h2

theorem frame_tri {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (x : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (xp : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)) (hext : A.Ext p x xp)
    (gG : Fin (r + 1) → Fin n → E) (gS : Fin (r + 1) → Fin n → (A.loc p).Ep)
    (u : Fin (r + 1) → (A.loc p).Ep) (hu : ∀ a, IsUnit (u a)) (heq : ∀ a, u a • gS a = A.bc p (gG a))
    (hstep : ∀ j : Fin (r + 1), xp (gS j) - gS j ∈ Submodule.span (A.loc p).Ep (gS '' {i | (i : ℕ) < j})) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, x (gG j) = ∑ i, s i j • gG i := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have key : ∀ j : Fin (r + 1), x (gG j) - gG j ∈ Submodule.span E (gG '' {i | (i : ℕ) < j}) := by
    intro j
    apply descend (A.loc p).ιE gG
    have e1 : (fun i => (A.loc p).ιE ((x (gG j) - gG j) i)) = u j • (xp (gS j) - gS j) := by
      rw [smul_sub, ← map_smul, heq, hext]
      funext i
      simp [Places.bc]
    rw [e1]
    refine Submodule.smul_mem _ _ ?_
    refine (Submodule.span_le.mpr ?_) (hstep j)
    rintro _ ⟨i, hi, rfl⟩
    have h3 : gS i = ((hu i).unit⁻¹ : ((A.loc p).Ep)ˣ) • A.bc p (gG i) := by
      rw [← heq, Units.smul_def, smul_smul, (hu i).val_inv_mul, one_smul]
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have key2 : ∀ j : Fin (r + 1), ∃ l : Fin (r + 1) →₀ E,
      l ∈ Finsupp.supported E E {i : Fin (r + 1) | (i : ℕ) < j} ∧
      Finsupp.linearCombination E gG l = x (gG j) - gG j := fun j =>
    (Finsupp.mem_span_image_iff_linearCombination E).mp (key j)
  choose l hl hl' using key2
  have hz : ∀ i j : Fin (r + 1), ¬ ((i : ℕ) < j) → l j i = 0 := fun i j h =>
    (Finsupp.mem_supported' _ _).mp (hl j) i h
  refine ⟨Matrix.of fun i j => if i = j then 1 else l j i, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
    simp only [Matrix.of_apply, if_neg hne]
    exact hz i j (by rw [Fin.lt_def] at hij; omega)
  · simp
  · have hjj : l j j = 0 := hz j j (lt_irrefl _)
    have hsplit : ∀ i, (if i = j then (1 : E) else l j i) = (if i = j then 1 else 0) + l j i := by
      intro i
      by_cases h : i = j
      · subst h; simp [hjj]
      · simp [h]
    have hlc := hl' j
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
    simp only [Matrix.of_apply, hsplit, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hlc]
    abel

theorem stab_unitriangular : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, ∃ s s' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ((∀ i j, j < i → s' i j = 0) ∧ (∀ i, s' i i = 1)) ∧ (∀ j, x (G.f j) = ∑ i, s i j • G.f i) ∧ ∀ j, x (G.f' j) = ∑ i, s' i j • G.f' i := by
  intro F E _ _ _ _ _ sig A r k G x hx
  obtain ⟨p⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩
  obtain ⟨xp, hxp, hext⟩ := (show ∀ p, ∃ g' ∈ (G.S p).St, A.Ext p x g' from hx) p
  have hxp' := Subgroup.mem_inf.mp hxp
  have hunit : ∀ a : Fin (r + 1), IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) := fun a =>
    ((G.c p).isUnit.pow _).map _
  obtain ⟨s, hs, hsx⟩ := frame_tri A p x xp hext G.f (G.S p).f _ hunit (G.f_eq p)
    (loc_step (G.S p) (G.S p).f (fun b hb => by
      rw [(G.S p).gram]
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.1)
  obtain ⟨s', hs', hsx'⟩ := frame_tri A p x xp hext G.f' (G.S p).f' _ hunit (G.f'_eq p)
    (loc_step (G.S p) (G.S p).f' (fun b hb => by
      rw [(G.S p).gram']
      have : b ≠ Fin.last r := fun h => by subst h; simp at hb
      simp [this]) xp hxp'.2)
  exact ⟨s, s', hs, hs', hsx, hsx'⟩

end GlobalTheory.HL.StTri
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GlueInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem nonempty_place' : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem nontrivial_Ep (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) : Nontrivial (A.loc p).Ep :=
  Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := nonempty_place' (F := F)
  haveI := nontrivial_Ep A p
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem sig_ne_id (A : Places F E sig) : ¬ ∀ y, sig y = y := by
  intro h
  obtain ⟨p⟩ := nonempty_place' (F := F)
  have hcj : (A.L p).cj.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range (A.loc p).span fun y => by
      simp [A.L_cj, (A.loc p).cj_ιE, h]
  have hall : ∀ z : (A.loc p).Ep, ∃ c : (A.loc p).Fp, c • (1 : (A.loc p).Ep) = z := fun z => by
    obtain ⟨a, ha⟩ := ((A.L p).cj_fix z).1 (by simpa using LinearMap.congr_fun hcj z)
    exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  have := finrank_le_one (1 : (A.loc p).Ep) hall
  rw [(A.loc p).rank] at this
  norm_num at this

theorem fix_mem (A : Places F E sig) (s : E) (hs : sig s = s) : ∃ t : F, algebraMap F E t = s := by
  by_contra hno
  push_neg at hno
  apply sig_ne_id A
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
      have hab' : algebraMap F E a + algebraMap F E b * s = 0 := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab; exact hab
      apply hno (-a / b)
      rw [map_div₀, map_neg, div_eq_iff hb']
      linear_combination (-1 : E) * hab'
  have hspan : Submodule.span F (Set.range ![(1 : E), s]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, A.quad]
    simp
  have hid : sig.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range hspan fun i => by
      fin_cases i <;> simp [hs]
  exact fun y => LinearMap.congr_fun hid y

theorem int_of_loc (A : Places F E sig) (t : F)
    (h : ∀ p, (A.loc p).ιE (algebraMap F E t) ∈ (A.L p).O) : t ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro p
  haveI := nontrivial_Ep A p
  have h1 := h p
  rw [(A.loc p).compat, (A.L p).O_def] at h1
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] ((A.loc p).ιF t) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h1
  have h3 := (Valuation.integer.integers (valuation (A.loc p).Fp)).mem_of_integral h2
  have h4 : (A.loc p).ιF t ≤ᵥ (A.loc p).ιF 1 := by
    rw [map_one]
    exact (Valuation.Compatible.vle_iff_le (v := valuation (A.loc p).Fp) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 h3)
  simpa using ((A.loc p).val t 1).1 h4

theorem sig_mem (A : Places F E sig) (y : E) (p : HeightOneSpectrum (𝓞 F))
    (hy : (A.loc p).ιE y ∈ (A.L p).O) : (A.loc p).ιE (sig y) ∈ (A.L p).O := by
  rw [← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).O_def]
  exact (((A.L p).O_def _).1 hy).map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

theorem isIntegral_of_quadratic (y a b : E) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (h : y ^ 2 - a * y + b = 0) : IsIntegral ℤ y := by
  have hR : IsIntegral (integralClosure ℤ E) y := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, ha⟩ : integralClosure ℤ E) * Polynomial.X +
      Polynomial.C (⟨b, hb⟩ : integralClosure ℤ E), by monicity!, ?_⟩
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul] using h
  exact isIntegral_trans y hR

end GlobalTheory.HL.GlueInt


open GlobalTheory.HL.GlueInt in
theorem GlobalTheory.HL.isIntegral_of_forall_mem_O : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) →
    IsIntegral ℤ y := by
  intro F E _ _ _ _ _ sig A y hy
  obtain ⟨a, ha⟩ := fix_mem A (y + sig y) (by rw [map_add (f := _), sig_sig A, add_comm])
  obtain ⟨b, hb⟩ := fix_mem A (y * sig y) (by rw [map_mul, sig_sig A, mul_comm])
  obtain ⟨a0, rfl⟩ := int_of_loc A a fun p => by
    rw [ha, map_add (f := _)]; exact (A.L p).O.add_mem (hy p) (sig_mem A y p (hy p))
  obtain ⟨b0, rfl⟩ := int_of_loc A b fun p => by
    rw [hb, map_mul]; exact (A.L p).O.mul_mem (hy p) (sig_mem A y p (hy p))
  refine isIntegral_of_quadratic y _ _ ((RingOfIntegers.isIntegral_coe a0).map (algebraMap F E).toIntAlgHom)
    ((RingOfIntegers.isIntegral_coe b0).map (algebraMap F E).toIntAlgHom) ?_
  change y ^ 2 - algebraMap F E (algebraMap (𝓞 F) F a0) * y + algebraMap F E (algebraMap (𝓞 F) F b0) = 0
  rw [ha, hb]
  ring
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Glue

theorem local_le_lat_of_approx {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (n : ℕ) (Λ : ∀ p, Submodule (A.L p).O (Fin n → (A.loc p).Ep))
    (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ)
    (hΓ : ∀ x, x ∈ Γ ↔ ∀ p, A.bc p x ∈ Λ p)
    (hN : ∀ p (v : Fin n → (A.loc p).Ep), (∀ i, v i ∈ (A.L p).O) → (N : (A.loc p).Ep) • v ∈ Λ p)
    (happ : ∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite →
      ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = (N : (A.loc p).Ep) * o) :
    ∀ p, Λ p ≤ A.lat p Γ := by
  intro p v hv
  have hsingle : ∀ i : Fin n, ((N : E) • (Pi.single i 1 : Fin n → E)) ∈ Γ := by
    intro i
    rw [hΓ]
    intro q
    have h1 : A.bc q ((N : E) • (Pi.single i 1 : Fin n → E)) =
        (N : (A.loc q).Ep) • (Pi.single i 1 : Fin n → (A.loc q).Ep) := by
      funext j
      simp only [Places.bc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [h1]
    apply hN
    intro j
    by_cases h : j = i
    · subst h; simp [Subring.one_mem]
    · simp [Pi.single_apply, h, Subring.zero_mem]
  have hint : ∀ w : Fin n → (A.loc p).Ep, (∀ i, w i ∈ (A.L p).O) →
      (N : (A.loc p).Ep) • w ∈ A.lat p Γ := by
    intro w hw
    have hw' : (N : (A.loc p).Ep) • w =
        ∑ i, (⟨w i, hw i⟩ : (A.L p).O) • A.bc p ((N : E) • (Pi.single i 1 : Fin n → E)) := by
      funext j
      simp [Places.bc, Subring.smul_def, Pi.single_apply, Finset.sum_apply, mul_comm]
      simp [apply_ite (A.loc p).ιE, mul_ite, Finset.sum_ite_eq, mul_comm]
    rw [hw']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle i, rfl⟩)
  have hfin : ∀ i, {q | (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q ∉ (A.L q).O}.Finite := by
    intro i
    apply (Set.finite_singleton p).subset
    intro q hq
    by_contra h
    apply hq
    rw [Pi.single_eq_of_ne h]
    exact (A.L q).O.zero_mem
  choose x hx using fun i => happ _ (hfin i)
  choose o ho hxo using hx
  have hbc : ∀ q, A.bc q (fun i => x i) =
      (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) + (N : (A.loc q).Ep) • (fun i => o i q) := by
    intro q
    funext i
    have h2 := hxo i q
    simp only [Places.bc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h2]
    ring
  have hX : (fun i => x i) ∈ Γ := by
    rw [hΓ]
    intro q
    rw [hbc q]
    refine (Λ q).add_mem ?_ (hN q _ fun i => ho i q)
    by_cases hq : q = p
    · subst hq
      simpa using hv
    · have h3 : (fun i => (Pi.single p (v i) : ∀ q, (A.loc q).Ep) q) = 0 := by
        funext i
        simp [Pi.single_eq_of_ne hq]
      rw [h3]
      exact (Λ q).zero_mem
  have hv' : v = A.bc p (fun i => x i) - (N : (A.loc p).Ep) • (fun i => o i p) := by
    rw [hbc p]
    funext i
    simp
  rw [hv']
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, hX, rfl⟩) (hint _ fun i => ho i p)

end GlobalTheory.HL.Glue
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace.UnitVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem vE_eq_zero_of_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : F}
    (hc : algebraMap F E c ∈ L.O) (hu : ∃ y ∈ L.O, algebraMap F E c * y = 1) :
    vE L ϖ (algebraMap F E c) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨y, hy, hcy⟩ := hu
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcy
    exact zero_ne_one hcy
  have hyc : y = algebraMap F E c⁻¹ := by
    have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    calc y = (algebraMap F E c⁻¹ * algebraMap F E c) * y := by rw [mul_comm (algebraMap F E c⁻¹), h1, one_mul]
      _ = algebraMap F E c⁻¹ * (algebraMap F E c * y) := by ring
      _ = algebraMap F E c⁻¹ := by rw [hcy, mul_one]
  have hci : c⁻¹ ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 (hyc ▸ hy)
  have hcO : c ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hc
  have h1 := (hint c hc0).2 hcO
  have h2 := (hint c⁻¹ (inv_ne_zero hc0)).2 hci
  have h11 := hadd 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h11
  have h3 := hadd c c⁻¹ hc0 (inv_ne_zero hc0)
  rw [mul_inv_cancel₀ hc0] at h3
  omega

end GlobalTheory.HL.StdPlace.UnitVal


open GlobalTheory.HL.StdPlace.UnitVal in
theorem GlobalTheory.HL.StdPlace.vE_G_D_eq_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hS
  obtain ⟨-, -, ⟨c, -, hGc⟩, -⟩ := GlobalTheory.FrameBasic.main L r k S
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hGc]
    obtain ⟨hG, y, hy, hGy⟩ := hS.G_unit
    exact vE_eq_zero_of_unit L S.ϖ_irr (hGc ▸ hG) ⟨y, hy, hGc ▸ hGy⟩
  · obtain ⟨hD, y, hy, hDy⟩ := hS.D_unit l hl
    obtain ⟨c, hc⟩ := GlobalTheory.UnramOrder.exists_norm L hD
    rw [hc]
    refine vE_eq_zero_of_unit L S.ϖ_irr (hc ▸ L.O.mul_mem hD (GlobalTheory.UnramOrder.cj_mem L hD))
      ⟨y * L.cj y, L.O.mul_mem hy (GlobalTheory.UnramOrder.cj_mem L hy), ?_⟩
    rw [← hc]
    calc S.D l * L.cj (S.D l) * (y * L.cj y) = (S.D l * y) * L.cj (S.D l * y) := by rw [map_mul]; ring
      _ = 1 := by rw [hDy, map_one, mul_one]
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.weil_integration_formula_orbit : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.WeilOrbit.weil_formula | exact GlobalTheory.WeilOrbit.weil_formula | (intros; apply GlobalTheory.WeilOrbit.weil_formula <;> assumption)
end
