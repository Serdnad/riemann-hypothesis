module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle007
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle233
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.PowerSeries.Basic
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
public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_algebraMap_eq_of_includeLeft_eq_includeRight :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B),
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b →
      ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ b hb
  have h := Algebra.IsEffective.of_faithfullyFlat A B
  have h0 : Algebra.TensorProduct.includeLeftSubRight A B b = 0 := by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using hb
  obtain ⟨a, ha⟩ := (h b).mp h0
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.EtC
end

section

open TensorProduct

namespace GlobalTheory.FlatDescent

theorem hilbert90_local_of_cocycle : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  intro R S _ _ _ _ _ _ c hc p hp
  classical
  let θ : S →ₗ[S] S ⊗[R] S := LinearMap.toSpanSingleton S (S ⊗[R] S) (c : S ⊗[R] S)
  have hθ : ∀ n, θ n = (n ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) := fun n => by
    simp [θ, Algebra.smul_def]

  let ψ : (S ⊗[R] S) ⊗[R] S →ₐ[R] S ⊗[R] S :=
    Algebra.TensorProduct.lift (S := R) (AlgHom.id R (S ⊗[R] S))
      (Algebra.TensorProduct.includeRight) (fun _ _ => Commute.all _ _)
  have h1 : ∀ x, ψ (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x) = x := by
    intro x; simp [ψ, ← Algebra.TensorProduct.one_def]
  have h2 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
      (AlgHom.id R S) x) = (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, tmul_add]
    | tmul a b => simp [ψ]
  have h3 : ∀ x, ψ (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
      (AlgHom.id R S) x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [ψ]
  have hμ : Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = 1 := by
    have h := congrArg ψ hc
    rw [map_mul, h1, h2, h3] at h
    have h' : (1 : S) ⊗ₜ[R] Algebra.TensorProduct.lmul' R (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] (1 : S) :=
      (Units.mul_right_inj c).1 (h.trans (mul_one _).symm)
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) S h'
  have hact : ∀ x, act R S S x = Algebra.TensorProduct.lmul' R x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp
  have hcounit : ∀ n, act R S S (θ n) = n := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', (act R S S).map_smul, hact, hμ, smul_eq_mul, mul_one]

  let e := (TensorProduct.assoc R S S S)
  have hL0 : ∀ (a b : S) (z : S ⊗[R] S), a ⊗ₜ[R] (b • z) =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (a ⊗ₜ[R] b) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) z) := by
    intro a b z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add, smul_add, tmul_add]
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeft_apply, AlgHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, e, TensorProduct.assoc_tmul, smul_tmul',
        smul_eq_mul]
  have hL : ∀ x : S ⊗[R] S, (θ.restrictScalars R).lTensor S x =
      e (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) x *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S))
          (AlgHom.id R S) (c : S ⊗[R] S)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars]
      exact hL0 a b _
  have hR : ∀ x : S ⊗[R] S, (TensorProduct.mk R S S 1).lTensor S x =
      e (Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S))
        (AlgHom.id R S) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [e]
  have hsmul : ∀ (g : S →ₗ[R] S ⊗[R] S) (n : S) (x : S ⊗[R] S),
      g.lTensor S (n • x) = n • g.lTensor S x := by
    intro g n x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
    | tmul a b => simp [smul_tmul']
  have hcoassoc : ∀ n, (θ.restrictScalars R).lTensor S (θ n) = (TensorProduct.mk R S S 1).lTensor S (θ n) := by
    intro n
    have hθ' : θ n = n • (c : S ⊗[R] S) := rfl
    rw [hθ', hsmul, hsmul, hL, hR, hc]
  have hD : IsDescentDatum θ := ⟨hcounit, hcoassoc⟩
  haveI : Module.Invertible R (invariants θ) := hD.invertible_invariants

  obtain ⟨f, m, hfm⟩ : ∃ (f : Module.Dual R (invariants θ)) (m : invariants θ), f m ∉ p := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨T, hT⟩ := ((Module.Invertible.linearEquiv R (invariants θ)).symm 1).exists_finset
    have h1 : (1 : R) = ∑ i ∈ T, i.1 i.2 := by
      have := congrArg (Module.Invertible.linearEquiv R (invariants θ)) hT

      simpa [Module.Invertible.linearEquiv, map_sum] using this
    exact hp.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.sum_mem _ fun i _ => hcon i.1 i.2))
  have hcomm : ∀ x : invariants θ, f m • x = f x • m := by
    intro x
    have := congrArg (TensorProduct.lift ((LinearMap.lsmul R (invariants θ)).comp f))
      (Module.Invertible.tmul_comm (m₁ := m) (m₂ := x))
    simpa using this
  obtain ⟨y, hy⟩ := hD.bijective_extend.2 1
  have hspan : ∀ y : S ⊗[R] invariants θ,
      algebraMap R S (f m) * extend S (invariants θ) y ∈ Ideal.span {(m : S)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), mul_add]; exact Ideal.add_mem _ hx hy
    | tmul b x =>
      have hx : algebraMap R S (f m) * (x : S) = algebraMap R S (f x) * (m : S) := by
        have := congrArg Subtype.val (hcomm x)
        simpa [Algebra.smul_def] using this
      rw [extend_tmul, smul_eq_mul, mul_left_comm, hx, ← mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (hspan y)
  refine ⟨f m, hfm, m, s, 1, ?_, ?_⟩
  · rw [← hθ]; exact mem_invariants.1 m.2
  · rw [pow_one, mul_comm, hs, hy, mul_one]

end GlobalTheory.FlatDescent
end

section

open IsLocalRing

namespace GlobalTheory.Mum

theorem exists_uniformiser_mul_eq_mul_pow_of_height_eq_one (O : Type) [CommRing O] [IsDomain O]
    [IsNoetherianRing O] [IsIntegrallyClosed O] (p : Ideal O) [hp : p.IsPrime] (h1 : p.height = 1)
    (h : O) (hh : h ≠ 0) :
    ∃ π ∈ p, π ≠ 0 ∧ (∀ y ∈ p, ∃ s ∉ p, π ∣ s * y) ∧
      ∃ (n : ℕ) (b c : O), b ∉ p ∧ c ∉ p ∧ b * h = c * π ^ n := by
  have := GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one O p h1
  let R := Localization.AtPrime p
  have hinj : Function.Injective (algebraMap O R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨⟨π, s⟩, hs⟩ := IsLocalization.surj p.primeCompl ϖ
  have hsu : IsUnit (algebraMap O R s) := IsLocalization.map_units R s
  have hπ : Irreducible (algebraMap O R π) := by
    have e : algebraMap O R π = ϖ * algebraMap O R s := hs.symm
    rw [e]
    exact (irreducible_mul_isUnit hsu).2 hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπ
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p π, hmax]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    exact hπ.ne_zero (map_zero _)
  · intro y hy
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff R p y, hmax, Ideal.mem_span_singleton] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨⟨t, r⟩, hr⟩ := IsLocalization.surj p.primeCompl z
    refine ⟨r, r.2, t, hinj ?_⟩
    have hr' : z * algebraMap O R r = algebraMap O R t := hr
    rw [map_mul, map_mul, hz, ← hr']
    ring
  · have hh' : algebraMap O R h ≠ 0 := fun h0 => hh (hinj (by rw [h0, map_zero]))
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh' hπ
    obtain ⟨⟨c, b⟩, hb⟩ := IsLocalization.surj p.primeCompl (u : R)
    have hb' : (u : R) * algebraMap O R b = algebraMap O R c := hb
    refine ⟨n, b, c, b.2, ?_, hinj ?_⟩
    · have hcu : IsUnit (algebraMap O R c) := by
        rw [← hb']
        exact u.isUnit.mul (IsLocalization.map_units R b)
      exact (IsLocalization.AtPrime.isUnit_to_map_iff R p c).1 hcu
    · rw [map_mul, map_mul, map_pow, hu, ← hb']
      ring

theorem exists_mul_eq_mul_sq_of_faithfullyFlat_of_map_isPrime : ∀ (O C : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [CommRing C] [IsDomain C] [IsNoetherianRing C] [Algebra O C] [Module.FaithfullyFlat O C] (h : O), h ≠ 0 → (∃ (u : Cˣ) (g : C), algebraMap O C h = u * g ^ 2) → ∀ p : Ideal O, p.IsPrime → p.height = 1 → (Ideal.map (algebraMap O C) p).IsPrime → ∃ a b c : O, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2 := by
  intro O C _ _ _ _ _ _ _ _ _ h hh hsq p hp h1 hP
  obtain ⟨u, g, hg⟩ := hsq
  obtain ⟨π, hπp, hπ0, hgen, n, b, c, hb, hc, hbc⟩ :=
    exists_uniformiser_mul_eq_mul_pow_of_height_eq_one O p h1 h hh
  let P : Ideal C := Ideal.map (algebraMap O C) p
  let R := Localization.AtPrime P
  let φ : O →+* R := (algebraMap C R).comp (algebraMap O C)
  have hcomap : P.comap (algebraMap O C) = p := Ideal.comap_map_eq_self_of_faithfullyFlat p
  have hinjR : Function.Injective (algebraMap C R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have hinjC : Function.Injective (algebraMap O C) := FaithfulSMul.algebraMap_injective O C
  have hinj : Function.Injective φ := hinjR.comp hinjC
  have hunit : ∀ s ∉ p, IsUnit (φ s) := by
    intro s hs
    refine (IsLocalization.AtPrime.isUnit_to_map_iff R P (algebraMap O C s)).2 ?_
    intro hm
    exact hs (hcomap ▸ (Ideal.mem_comap.2 hm))
  have hπR : φ π ≠ 0 := fun h0 => hπ0 (hinj (by rw [h0, map_zero]))
  have hmax : maximalIdeal R = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro y hy
      obtain ⟨s, hs, hd⟩ := hgen y hy
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      have hd' : φ π ∣ φ s * φ y := by rw [← map_mul]; exact map_dvd φ hd
      exact (hunit s hs).dvd_mul_left.1 hd'
    · rw [Ideal.span_singleton_le_iff_mem]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P (algebraMap O C π)).2
        (Ideal.mem_map_of_mem _ hπp)
  have hnf : ¬ IsField R := by
    intro hf
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot] at hf
    exact hπR hf
  have hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).1 (show (maximalIdeal R).IsPrincipal from ⟨⟨φ π, hmax⟩⟩)
  have hirr : Irreducible (φ π) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  have hhR : φ h = algebraMap C R u * algebraMap C R g ^ 2 := by
    show algebraMap C R (algebraMap O C h) = _
    rw [hg, map_mul, map_pow]
  have hg0 : algebraMap C R g ≠ 0 := by
    intro h0
    apply hh
    apply hinj
    rw [hhR, h0, map_zero]
    ring
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hg0 hirr
  have huR : IsUnit (algebraMap C R u) := u.isUnit.map _
  have hnm : 2 * m = n := by
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hirr hirr
      ((hunit b hb).unit * huR.unit * v ^ 2) (hunit c hc).unit _ _ ?_
    have e := congrArg φ hbc
    rw [map_mul, map_mul, map_pow, hhR, hv] at e
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [← e]
    ring
  refine ⟨π ^ m, b, c, hb, hc, ?_⟩
  rw [hbc, ← hnm]
  ring

end GlobalTheory.Mum
end

section

open IsLocalRing

theorem _root_.GlobalTheory.T.height_one_prime_associate : ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [IsDomain B'] [IsNoetherianRing B']
    [IsIntegrallyClosed B'] [Algebra A' B'] (𝔭 : Ideal A'), (𝔭.map (algebraMap A' B')).IsPrime →
    (𝔭.map (algebraMap A' B')).height = 1 → ∀ c : B', c ≠ 0 →
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  first | (exact @GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (exact GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one) | (intros; apply GlobalTheory.exists_locally_associated_algebraMap_of_height_eq_one <;> assumption)
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

variable {A B R : Type} [CommRing A] [CommRing B] [CommRing R]

def IsRingHomMod (π : B →+* A) (β : B →+* R) (n : ℕ) (φ : A → PowerSeries R) : Prop :=
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f * g) - φ f * φ g) ∧
  (∀ f g, (X : PowerSeries R) ^ n ∣ φ (f + g) - (φ f + φ g)) ∧
  (X : PowerSeries R) ^ n ∣ φ 1 - 1 ∧
  (∀ b, (X : PowerSeries R) ^ n ∣ φ (π b) - C (β b))

def IsJet (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (n : ℕ)
    (φ : A → PowerSeries R) : Prop :=
  IsRingHomMod π β n φ ∧
  (∀ f, (X : PowerSeries R) ^ n ∣ φ (m f) - rescale 2 (φ f)) ∧
  (∀ f, constantCoeff (φ f) = β (ε f)) ∧
  (∀ f, coeff 1 (φ f) = δ f)

theorem deriv_comp_m (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (E : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (hE : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f) (hEπ : ∀ a, E (π a) = 0) (f : A) :
    E (m f) = 2 * E f := by
  have hsq : ∀ x ∈ RingHom.ker ε ^ 2, E x = 0 := by
    intro x hx
    rw [pow_two] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [RingHom.mem_ker] at ha hb
      rw [hE, ha, hb]; simp
    · rw [map_add (f := _), ha, hb, add_zero]
  have hk : f - π (ε f) ∈ RingHom.ker ε := by
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply ε π, hεπ, RingHom.id_apply, sub_self]
  have h1 : m f = π (ε f) + (m (f - π (ε f)) - 2 * (f - π (ε f))) + (f - π (ε f)) + (f - π (ε f)) := by
    have : m (π (ε f)) = π (ε f) := by rw [← RingHom.comp_apply m π, hmπ]
    rw [map_sub, this]; ring
  have h2 : f = π (ε f) + (f - π (ε f)) := by ring
  rw [h1, map_add (f := _), map_add (f := _), map_add (f := _), hEπ, hsq _ (hm2 _ hk)]
  conv_rhs => rw [h2, map_add (f := _), hEπ]
  ring

end GlobalTheory.Nef.PathJet
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem coeff_mul_of_coeff_lt_eq_zero {R : Type} [CommRing R] (φ δ : PowerSeries R) (j : ℕ)
    (h : ∀ i < j, PowerSeries.coeff i δ = 0) :
    PowerSeries.coeff j (φ * δ) = PowerSeries.constantCoeff φ * PowerSeries.coeff j δ := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (0, j)]
  · simp
  · rintro ⟨a, b⟩ hp hne
    have hp : a + b = j := by simpa using hp
    have hb : b < j := by
      by_contra hb
      have ha : a = 0 := by omega
      have hb' : b = j := by omega
      subst ha hb'
      exact hne rfl
    rw [h _ hb, mul_zero]
  · intro hn
    exact absurd (by simp) hn

theorem ringHom_powerSeries_eq_of_rescale :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (c : R) (n : ℕ), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → 0 < n → (∀ j, n ≤ j → IsUnit (c ^ j - 2)) → ∀ γ γ' : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β → γ'.comp π = PowerSeries.C.comp β → PowerSeries.constantCoeff.comp γ = β.comp ε → PowerSeries.constantCoeff.comp γ' = β.comp ε → (PowerSeries.rescale c).comp γ = γ.comp m → (PowerSeries.rescale c).comp γ' = γ'.comp m → (∀ j < n, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f)) → γ = γ' := by
  intro A B R _ _ _ π ε m β c n hεπ hmπ _hεm hm hn hc γ γ' hγπ hγ'π hγ0 hγ'0 hγm hγ'm hlow
  have hεπ' : ∀ b, ε (π b) = b := fun b => by simpa using RingHom.congr_fun hεπ b
  have hmπ' : ∀ b, m (π b) = π b := fun b => by simpa using RingHom.congr_fun hmπ b
  have hγπ' : ∀ b, γ (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγπ b
  have hγ'π' : ∀ b, γ' (π b) = PowerSeries.C (β b) := fun b => by simpa using RingHom.congr_fun hγ'π b
  have hc0 : ∀ f, PowerSeries.constantCoeff (γ f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ0 f
  have hc0' : ∀ f, PowerSeries.constantCoeff (γ' f) = β (ε f) := fun f => by
    simpa using RingHom.congr_fun hγ'0 f
  have hγm' : ∀ f, γ (m f) = PowerSeries.rescale c (γ f) := fun f => by
    simpa using (RingHom.congr_fun hγm f).symm
  have hγ'm' : ∀ f, γ' (m f) = PowerSeries.rescale c (γ' f) := fun f => by
    simpa using (RingHom.congr_fun hγ'm f).symm
  have hcoeff : ∀ j, ∀ f, PowerSeries.coeff j (γ f) = PowerSeries.coeff j (γ' f) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    rcases lt_or_ge j n with hj | hj
    · exact hlow j hj
    have hj0 : j ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D : A → R, ∀ f, D f = PowerSeries.coeff j (γ f) - PowerSeries.coeff j (γ' f) :=
      ⟨_, fun _ => rfl⟩
    have hlowδ : ∀ f, ∀ i < j, PowerSeries.coeff i (γ f - γ' f) = 0 := by
      intro f i hi; rw [map_sub, ih i hi f, sub_self]
    have Dadd : ∀ f g, D (f + g) = D f + D g := by
      intro f g; simp only [hD, map_add (f := _)]; ring
    have Dsub : ∀ f g, D (f - g) = D f - D g := by
      intro f g; simp only [hD, map_sub]; ring
    have Dmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := by
      intro f g
      have e : γ (f * g) - γ' (f * g) = γ f * (γ g - γ' g) + γ' g * (γ f - γ' f) := by
        rw [map_mul, map_mul]; ring
      have h1 := coeff_mul_of_coeff_lt_eq_zero (γ f) _ j (hlowδ g)
      have h2 := coeff_mul_of_coeff_lt_eq_zero (γ' g) _ j (hlowδ f)
      have h3 : D (f * g) = PowerSeries.coeff j (γ (f * g) - γ' (f * g)) := by
        rw [hD, map_sub]
      rw [h3, e, map_add (f := _), h1, h2, hc0, hc0', map_sub, map_sub, hD, hD]
    have Dπ : ∀ b, D (π b) = 0 := by
      intro b; rw [hD, hγπ', hγ'π', PowerSeries.coeff_C, if_neg hj0, sub_self]
    have Dsq : ∀ x ∈ RingHom.ker ε ^ 2, D x = 0 := by
      intro x hx
      rw [pow_two] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [RingHom.mem_ker] at ha hb
        rw [Dmul, ha, hb, map_zero, zero_mul, zero_mul, add_zero]
      · intro x y hx hy
        rw [Dadd, hx, hy, add_zero]
    have Dm2 : ∀ f, D (m f) = 2 * D f := by
      intro f
      set f0 := f - π (ε f) with hf0
      have hf0k : f0 ∈ RingHom.ker ε := by
        rw [RingHom.mem_ker, hf0, map_sub, hεπ', sub_self]
      have hmf : m f = π (ε f) + m f0 := by
        rw [hf0, map_sub, hmπ']; ring
      have hff : f = π (ε f) + f0 := by rw [hf0]; ring
      have hDf : D f = D f0 := by
        conv_lhs => rw [hff]
        rw [Dadd, Dπ, zero_add]
      have hsplit : m f0 = (m f0 - 2 * f0) + (f0 + f0) := by ring
      rw [hmf, Dadd, Dπ, zero_add, hsplit, Dadd, Dsq _ (hm f0 hf0k), Dadd, hDf]
      ring
    have Dmc : ∀ f, D (m f) = c ^ j * D f := by
      intro f
      rw [hD, hD, hγm', hγ'm', PowerSeries.coeff_rescale, PowerSeries.coeff_rescale]
      ring
    intro f
    have h0 : (c ^ j - 2) * D f = 0 := by
      have := (Dmc f).symm.trans (Dm2 f)
      rw [sub_mul, this, sub_self]
    have hDf0 : D f = 0 := (hc j hj).mul_right_eq_zero.mp h0
    rw [hD] at hDf0
    exact sub_eq_zero.mp hDf0
  exact RingHom.ext fun f => PowerSeries.ext fun j => hcoeff j f

end GlobalTheory.Nef
end
