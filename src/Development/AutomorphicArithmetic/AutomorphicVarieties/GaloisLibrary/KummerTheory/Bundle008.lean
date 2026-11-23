module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem UpperTheory.V.Kum.coc_conj_triv {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h k : Γ)
    (e : k * g = g * h) (hk : ∀ m, ρ k m = m) : f k = ρ g (f h) := by
  have h1 := hf k g
  rw [e, hf, hk, add_comm] at h1
  exact (add_right_cancel h1).symm

theorem UpperTheory.V.Kum.resInfMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), (Sha D e).map (resInf D e) ≤ EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g := fun g => DFunLike.congr_fun D.hchi g
  have htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
    rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
  have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
  have hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 →
      z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h)) := fun g h k e1 hk =>
    coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)
  have h1 : z.1 1 = 0 := by
    have := hz 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l, u.1 ∈ Dec (F := F) A →
      z.1 (toGS Ω _ u.1) = 0 := by
    intro A hA u hu
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by
      have := (p4 A v l hv).1 hA
      rw [← D.hS] at this
      exact this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e ⟨v, hvS⟩ z).1 ((mem_Sha_iff D e _).1 hx ⟨v, hvS⟩)
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := by
      have h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩ := hu
      show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    have hu1 : cycZ F Ω l u.1 = 1 := u.2.2
    have h2 := hm ⟨_, hc⟩
    rw [htriv _ (by simp [hu1]), sub_self] at h2
    rw [hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]
  refine ⟨⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))
  · rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  · rw [resInf_mk]
    by_cases hA : A = ⊤
    · subst hA
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, h1]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]
      exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hu⟩
    have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [this, h1]
  · rw [resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]
    rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem finSupp {K : Type} [Field K] [NumberField K] {G : Type} [CommGroup G]
    (g : HeightOneSpectrum (𝓞 K) → G) (n : ℤ) (a : Kˣ) :
    Function.HasFiniteMulSupport fun v => g v ^ (ordv v a / n) := by
  refine ((clProd K).2.2.1 a).subset fun v hv => ?_
  intro h
  apply hv
  simp [h]

private theorem mk_radCl {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) (a : Kˣ) :
    (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / n) := by
  have h := (QuotientGroup.mk' (clSub S)).map_finprod (finSupp primeCl (n : ℤ) a)
  simpa [radCl] using h

private theorem mk_primeCl {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)

private theorem ordv_pow' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) :
    ordv v (b ^ n) = n * ordv v b := by
  induction n with
  | zero => simp [ordv_one]
  | succ m ih => rw [pow_succ, ordv_mul, ih]; push_cast; ring

theorem UpperTheory.V.Kum.radClMul :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → (∀ a ∈ SelK S n, ∀ b ∈ SelK S n, (QuotientGroup.mk (radCl n (a * b)) : ClS S) = QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b)) ∧
    (∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1) ∧ (∀ a b : Kˣ, radCl n (a * b ^ n) = radCl n a) := by
  intro K _ _ S n hn
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have h1 : ∀ x : Kˣ, radCl 1 x = 1 := (clProd K).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mk_radCl S n, mk_radCl S n, mk_radCl S n,
      ← finprod_mul_distrib (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)
        (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) b)]
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simp [mk_primeCl hv]
    · rw [ordv_mul, Int.add_ediv_of_dvd_right (hb v hv), zpow_add]
  · intro a ha
    have e := mk_radCl S 1 a
    rw [h1 a] at e
    simp only [Nat.cast_one, Int.ediv_one, QuotientGroup.mk_one] at e
    have key : ∀ v : HeightOneSpectrum (𝓞 K),
        ((QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / (n : ℤ))) ^ n =
          (QuotientGroup.mk (primeCl v) : ClS S) ^ ordv v a := by
      intro v
      by_cases hv : v ∈ S
      · simp [mk_primeCl hv]
      · rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (ha v hv)]
    rw [mk_radCl S n, finprod_pow (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a),
      finprod_congr key]
    exact e.symm
  · intro a b
    have e := h1 b
    simp only [radCl, Nat.cast_one, Int.ediv_one] at e
    have hb1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) => primeCl v ^ ordv v b := by
      have h := finSupp (primeCl (K := K)) 1 b
      simpa only [Int.ediv_one] using h
    simp only [radCl]
    rw [finprod_congr (fun v => show primeCl v ^ (ordv v (a * b ^ n) / (n : ℤ)) =
        primeCl v ^ (ordv v a / (n : ℤ)) * primeCl v ^ ordv v b by
          rw [ordv_mul, ordv_pow', Int.add_mul_ediv_left _ _ hn', zpow_add]),
      finprod_mul_distrib (finSupp primeCl (n : ℤ) a) hb1, e, mul_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_frac_of_mem {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (c : ClassGroup (𝓞 K)) (hc : c ∈ clSub S) :
    ∃ J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K J = c ∧
      ∀ v ∉ S, FractionalIdeal.count K v J.1 = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩,
      ClassGroup.mk_mk0 _ _, fun v hv => ?_⟩
    rw [FractionalIdeal.coe_mk0]
    exact FractionalIdeal.count_maximal_coprime K v (fun h : w = v => hv (h ▸ hw))
  | one => exact ⟨1, map_one _, fun v _ => FractionalIdeal.count_one K v⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun v hv => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

private theorem mk_finprod_congr {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite) (hg : {v | g v ≠ 0}.Finite)
    (h : ∀ v ∉ S, f v = g v) :
    (QuotientGroup.mk (∏ᶠ v, primeCl v ^ f v) : ClS S) = QuotientGroup.mk (∏ᶠ v, primeCl v ^ g v) := by
  have hfm : ∀ f : HeightOneSpectrum (𝓞 K) → ℤ, {v | f v ≠ 0}.Finite →
      Function.HasFiniteMulSupport (fun v => primeCl v ^ f v) := by
    intro f hf
    unfold Function.HasFiniteMulSupport
    apply hf.subset
    intro v hv
    simp only [Set.mem_setOf_eq]
    intro h0
    exact hv (by simp [h0])
  have e1 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)
  have e2 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)
  simp only [QuotientGroup.mk'_apply] at e1 e2
  rw [e1, e2]
  apply finprod_congr
  intro v
  by_cases hv : v ∈ S
  · have h1 : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)
    simp [QuotientGroup.mk_zpow, h1]
  · rw [h v hv]

theorem UpperTheory.V.Kum.radClSurj :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → ∀ c : ClS S, c ^ n = 1 → ∃ a ∈ SelK S n, QuotientGroup.mk (radCl n a) = c := by
  intro K _ _ S n hn c hc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x :=
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hc
  obtain ⟨J, hJ, hJS⟩ := exists_frac_of_mem S _ hc
  have hP : ClassGroup.mk K (I ^ n * J⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hJ, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at hP
  obtain ⟨y, hy⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hP
  have hx' : ((I ^ n * J⁻¹ : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = FractionalIdeal.spanSingleton _ y :=
    FractionalIdeal.coeToSubmodule_injective (hy.trans (FractionalIdeal.coe_spanSingleton _ y).symm)
  have hy0 : y ≠ 0 := by
    intro h0
    apply Units.ne_zero (I ^ n * J⁻¹)
    rw [hx', h0, FractionalIdeal.spanSingleton_zero]
  let a : Kˣ := Units.mk0 y hy0
  have hcount : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v (I : FractionalIdeal _ K) := by
    intro v hv
    rw [← (clProd K).2.1 v a]
    show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _
    rw [← hx', Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_inv, hJS v hv, neg_zero, add_zero]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine ⟨a, fun v hv => ⟨FractionalIdeal.count K v (I : FractionalIdeal _ K), hcount v hv⟩, ?_⟩
  rw [(clProd K).1 I]
  unfold radCl
  apply mk_finprod_congr S
  · apply ((clProd K).2.2.1 a).subset
    intro v hv h0
    apply hv
    simp [h0]
  · have hf := FractionalIdeal.finite_factors (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [Filter.eventually_cofinite] at hf
    exact hf
  · intro v hv
    rw [hcount v hv, Int.mul_ediv_cancel_left _ hn']
end
