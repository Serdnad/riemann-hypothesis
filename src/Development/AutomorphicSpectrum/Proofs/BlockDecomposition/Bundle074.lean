module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle051
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle060
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle041
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

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_of_isCompl : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T]
    (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := by
  intro p _ B _ T _ π g hC hB
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hT : (p : T) = 0 := by rw [← map_natCast g p, hB.char, map_zero]
  obtain ⟨FB, hFB⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char 1
  obtain ⟨FT, hFT⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hT 1
  have subB : ∀ x y : B, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FB x y
    simpa only [hFB, pow_one] using h
  have subT : ∀ x y : T, (x - y) ^ p = x ^ p - y ^ p := fun x y => by
    have h := map_sub FT x y
    simpa only [hFT, pow_one] using h
  have surj' : ∀ (M : ℕ) (y : T), ∃ x, g π ^ M ∣ y - g x := fun M y => by
    obtain ⟨x, hx⟩ := hC.surj M y
    exact ⟨x, Ideal.mem_span_singleton.1 hx⟩
  have inj' : ∀ (M : ℕ) (x : B), g π ^ M ∣ g x → π ^ M ∣ x := fun M x h =>
    Ideal.mem_span_singleton.1 (hC.inj M x (Ideal.mem_span_singleton.2 h))
  have root : ∀ (M : ℕ) (b : B), π ^ (p * M) ∣ b ^ p → π ^ M ∣ b := by
    rintro M b ⟨c, hc⟩
    obtain ⟨d, hd⟩ := hB.bij.2 c
    have hd' : d ^ p = c := hd
    refine ⟨d, hB.bij.1 (show b ^ p = (π ^ M * d) ^ p from ?_)⟩
    rw [hc, mul_pow, ← pow_mul, mul_comm M p, hd']
  have haus : ∀ x : T, (∀ n : ℕ, g π ^ n ∣ x) → x = 0 := by
    intro x hx
    refine hC.compl.toIsHausdorff.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hx n
  have dvdp : ∀ (n : ℕ) (x : T), g π ^ n ∣ x → g π ^ n ∣ x ^ p := fun n x h =>
    h.trans (dvd_pow_self x hp0.ne')
  refine ⟨hT, ?_, ?_⟩
  · intro z w hzw
    have hzw' : z ^ p = w ^ p := hzw
    rw [← sub_eq_zero]
    have h0 : (z - w) ^ p = 0 := by rw [subT, hzw', sub_self]
    apply haus
    intro M
    obtain ⟨b, hb⟩ := surj' (p * M) (z - w)
    have h1 : g π ^ (p * M) ∣ g (b ^ p) := by
      have h2 : (z - w - g b) ^ p = (z - w) ^ p - g b ^ p := subT _ _
      rw [h0, zero_sub] at h2
      have h3 : g π ^ (p * M) ∣ (z - w - g b) ^ p := dvdp _ _ hb
      rw [h2, dvd_neg] at h3
      rwa [map_pow]
    have h4 : π ^ M ∣ b := root M b (inj' _ _ h1)
    have h5 : g π ^ M ∣ g b := by
      rw [← map_pow]
      exact map_dvd g h4
    have h6 : g π ^ M ∣ z - w - g b := (pow_dvd_pow _ (Nat.le_mul_of_pos_left M hp0)).trans hb
    have h7 := dvd_add h6 h5
    rwa [sub_add_cancel] at h7
  · intro y
    choose b hb using fun M : ℕ => surj' (p * M) y
    choose e he using fun M : ℕ => hB.bij.2 (b M)
    have he' : ∀ M, e M ^ p = b M := he
    have cauchy : ∀ m n : ℕ, m ≤ n → π ^ m ∣ e m - e n := by
      intro m n hmn
      apply root
      rw [subB, he', he']
      apply inj'
      have h1 : g π ^ (p * m) ∣ y - g (b n) :=
        (pow_dvd_pow _ (Nat.mul_le_mul le_rfl hmn)).trans (hb n)
      have h2 := dvd_sub h1 (hb m)
      rw [map_sub]
      convert h2 using 1
      ring
    obtain ⟨L, hL⟩ := hC.compl.toIsPrecomplete.prec (f := fun n => g (e n)) (fun {m n} hmn => by
      beta_reduce
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, ← map_sub, ← map_pow]
      exact map_dvd g (cauchy m n hmn))
    refine ⟨L, ?_⟩
    show L ^ p = y
    rw [← sub_eq_zero]
    apply haus
    intro n
    have hn : g π ^ n ∣ g (e n) - L := by
      have h3 := hL n
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h3
    have h1 : g π ^ n ∣ (g (e n) - L) ^ p := dvdp _ _ hn
    rw [subT, ← map_pow g (e n) p, he'] at h1
    have h2 : g π ^ n ∣ y - g (b n) :=
      (pow_dvd_pow _ (Nat.le_mul_of_pos_left n hp0)).trans (hb n)
    have h4 := dvd_add h1 h2
    rw [← dvd_neg]
    convert h4 using 1
    ring

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SnakeCov

theorem prodLeft_eq_rTensor {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] (w : (B₁ × B₂) ⊗[A] K) :
    TensorProduct.prodLeft A A B₁ B₂ K w =
      ((LinearMap.fst A B₁ B₂).rTensor K w, (LinearMap.snd A B₁ B₂).rTensor K w) := by
  induction w with
  | tmul b k =>
    obtain ⟨b₁, b₂⟩ := b
    simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Prod.mk_add_mk]

theorem tensor_prod_ext {A B₁ B₂ K : Type} [CommRing A] [AddCommGroup B₁] [Module A B₁]
    [AddCommGroup B₂] [Module A B₂] [AddCommGroup K] [Module A K] {w w' : (B₁ × B₂) ⊗[A] K}
    (h₁ : (LinearMap.fst A B₁ B₂).rTensor K w = (LinearMap.fst A B₁ B₂).rTensor K w')
    (h₂ : (LinearMap.snd A B₁ B₂).rTensor K w = (LinearMap.snd A B₁ B₂).rTensor K w') :
    w = w' := by
  apply (TensorProduct.prodLeft A A B₁ B₂ K).injective
  rw [prodLeft_eq_rTensor, prodLeft_eq_rTensor, h₁, h₂]

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := by
  intro p _ A _ B₁ _ _ B₂ _ _ D _ _ r ρ₁ ρ₂ hr hD hsurj hK
  let ρ : (B₁ × B₂) →ₗ[A] D :=
    ρ₁.toLinearMap ∘ₗ LinearMap.fst A B₁ B₂ - ρ₂.toLinearMap ∘ₗ LinearMap.snd A B₁ B₂
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨b₁, b₂, rfl⟩ := hsurj y
    exact ⟨(b₁, b₂), by simp [ρ]⟩
  have h1 : ρ 1 = 0 := by simp [ρ]
  refine mv_cov p A (B₁ × B₂) D r ρ hr hD hρ h1 ?_
  intro K _ _ hPK
  obtain ⟨hinj, hker⟩ := hK K hPK
  have hf : ∀ a : K, (LinearMap.fst A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₁) ⊗ₜ[A] a := by
    intro a; simp
  have hs : ∀ a : K, (LinearMap.snd A B₁ B₂).rTensor K ((1 : B₁ × B₂) ⊗ₜ[A] a) = (1 : B₂) ⊗ₜ[A] a := by
    intro a; simp
  refine ⟨fun a ha => hinj a ?_ ?_, fun w hw => ?_⟩
  · rw [← hf, ha, map_zero]
  · rw [← hs, ha, map_zero]
  · have hcomm : ∀ t : (B₁ × B₂) ⊗[A] K, ρ.rTensor K t =
        Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) ((LinearMap.fst A B₁ B₂).rTensor K t) -
          Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) ((LinearMap.snd A B₁ B₂).rTensor K t) := by
      intro t
      induction t with
      | tmul b k => simp [ρ, TensorProduct.sub_tmul]
      | add x y hx hy =>
        simp only [map_add (f := _), hx, hy]
        abel
    have heq := hcomm w
    rw [hw, eq_comm, sub_eq_zero] at heq
    obtain ⟨a, ha₁, ha₂⟩ := hker _ _ heq
    exact ⟨a, tensor_prod_ext (by rw [ha₁, hf]) (by rw [ha₂, hs])⟩

end GlobalTheory.CompanionTheory.SnakeCov
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem frobenius_symm_smul {p : ℕ} {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    (FA : A ≃+* A) (hFA : ∀ x, FA x = x ^ p) (FC : C ≃+* C) (hFC : ∀ x, FC x = x ^ p)
    (a : A) (c : C) : FC.symm (a • c) = FA.symm a • FC.symm c := by
  apply FC.injective
  rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a),
    RingEquiv.apply_symm_apply]

private theorem exists_ringEquiv_frobenius_of_pf (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (h : Pf p A) :
    ∃ F : A ≃+* A, ∀ x, F x = x ^ p := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  have hb : Function.Bijective g := by
    have e : (g : A → A) = fun x => x ^ p := funext hg'
    rw [e]
    exact h.bij
  exact ⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩

theorem pf_tensor : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B]
    [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K →
    Pf p (B ⊗[A] K) := by
  intro p _ A _ B _ _ K _ _ hA hB hK
  obtain ⟨FA, hFA⟩ := exists_ringEquiv_frobenius_of_pf p A hA
  obtain ⟨FB, hFB⟩ := exists_ringEquiv_frobenius_of_pf p B hB
  obtain ⟨FK, hFK⟩ := exists_ringEquiv_frobenius_of_pf p K hK
  have hchar : (p : B ⊗[A] K) = 0 := by
    have h := map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p
    rw [← h, hB.char, map_zero]
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  let f : B →+ K →+ B ⊗[A] K :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k)
      (fun k k' => by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun b b' => by
        ext k
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.add_tmul])
  have hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k) := by
    intro a b k
    simp only [f, AddMonoidHom.mk'_apply]
    rw [frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]
  have hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b k =>
      rw [hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]
      simp only [f, AddMonoidHom.mk'_apply]
      rw [← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hgfun : (fun x : B ⊗[A] K => x ^ p) = g := funext fun x => (hg' x).symm
  refine ⟨hchar, ?_⟩
  rw [hgfun]
  refine ⟨Function.LeftInverse.injective hψ, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero g⟩
  | tmul b k =>
    obtain ⟨b', hb'⟩ := hB.bij.2 b
    obtain ⟨k', hk'⟩ := hK.bij.2 k
    have hb'' : b' ^ p = b := hb'
    have hk'' : k' ^ p = k := hk'
    refine ⟨b' ⊗ₜ[A] k', ?_⟩
    rw [hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add (f := _), hx', hy']⟩

end GlobalTheory.CompanionTheory.PerfectRing
end

section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Dblock

theorem smul_mem_range_lTensor_of_lTensor_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R)
      (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀]
      (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂]
      (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂)
      (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) →
      (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) →
      (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) →
      (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) →
      ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := by
  intro p _ R _ _ _ r N _ _ K₀ _ _ K₁ _ _ K₂ _ _ K₃ _ _ d₀ d₁ d₂ hr hdd h1 h2 h3 w hw k
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hrk : ∀ k, r k = r (k + 1) ^ (p - 2) * (r (k + 1) * r (k + 1)) := by
    intro k
    rw [← pow_two, ← pow_add, Nat.sub_add_cancel hp]
    exact (hr k).symm
  have hsat : ∀ (a : R) (x : K₂), a ≠ 0 → a • x ∈ LinearMap.range d₁ →
      ∀ k, r k • x ∈ LinearMap.range d₁ := by
    rintro a x ha ⟨y, hy⟩ k
    have hax : a • d₂ x = 0 := by
      rw [← map_smul, ← hy, hdd]
    have h0 : d₂ (r (k + 1) • x) = 0 := by
      rw [map_smul]
      exact h3 a _ ha hax (k + 1)
    have h4 := h2 _ h0 (k + 1)
    rw [hrk k, mul_smul, mul_smul]
    exact Submodule.smul_mem _ _ h4
  have hsub : (LinearMap.range d₁).subtype ∘ₗ d₁.rangeRestrict = d₁ := by
    ext x
    rfl
  have hw' : (LinearMap.range d₁).subtype.lTensor N (d₁.rangeRestrict.lTensor N w) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]
    exact hw
  have h5 := smul_eq_zero_of_lTensor_subtype_eq_zero R r N K₂ (LinearMap.range d₁) hsat _ hw' (k + 1)
  have h6 : d₁.rangeRestrict.lTensor N (r (k + 1) • w) = 0 := by
    rw [map_smul]
    exact h5
  have hex : Function.Exact (LinearMap.ker d₁).subtype d₁.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hx' : d₁ x = 0 := congrArg Subtype.val hx
      exact ⟨⟨x, hx'⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact Subtype.ext z.2
  obtain ⟨u, hu⟩ := (lTensor_exact N hex d₁.surjective_rangeRestrict _).1 h6
  have h7 : ∀ u : N ⊗[R] LinearMap.ker d₁,
      r (k + 1) • (LinearMap.ker d₁).subtype.lTensor N u ∈ LinearMap.range (d₀.lTensor N) := by
    intro u
    induction u with
    | tmul n z =>
      obtain ⟨y, hy⟩ := h1 z z.2 (k + 1)
      exact ⟨n ⊗ₜ y, by simp [hy, TensorProduct.tmul_smul]⟩
    | add a b ha hb =>
      rw [map_add (f := _), smul_add]
      exact Submodule.add_mem _ ha hb
  rw [hrk k, mul_smul, mul_smul, ← hu]
  exact Submodule.smul_mem _ _ (h7 u)

end GlobalTheory.CompanionTheory.Dblock
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.isProper_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => IsProper f) := by
  first | exact @GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | exact GlobalTheory.CompanionTheory.SpreadingModels.properSpreads | (intros; apply GlobalTheory.CompanionTheory.SpreadingModels.properSpreads <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

theorem _root_.GlobalTheory.T.smooth_spreads_out : GlobalTheory.SpreadingModels.Spreads (fun _ _ f => Smooth f) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | exact GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads | (intros; apply GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.TwExact

theorem twMap_range_eq_ker : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ →
    ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) →
    (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧
      IsCompact (L : Set G)) →
    ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v))
      (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g →
    LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  intro G V₁ V₂ V₃ _ _ _ _ _ _ _ _ _ ρ₁ ρ₂ ρ₃ h₁ h₂ h₃ N θ hθ hN f g hf hg hfg
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₁ N θ) x
    rw [LinearMap.mem_ker]
    have hv : g (f v) = 0 := by
      have h0 : f v ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f v
      exact LinearMap.mem_ker.mp h0
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, hv, Submodule.Quotient.mk_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective (GlobalTheory.PRep.twKer ρ₂ N θ) x
    rw [LinearMap.mem_ker] at hx
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    have hKinv : ∀ x : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (ρ₂ x) := by
      intro x u hu
      rw [Submodule.mem_comap, LinearMap.mem_ker, hg, LinearMap.mem_ker.mp hu, map_zero]
    let ρq : Representation ℂ G (V₂ ⧸ LinearMap.ker g) :=
      { toFun := fun x => (LinearMap.ker g).mapQ (LinearMap.ker g) (ρ₂ x) (hKinv x)
        map_one' := by
          ext u
          simp
        map_mul' := by
          intro x y
          ext u
          simp [Module.End.mul_apply] }
    have hq : GlobalTheory.PRep.IsSmooth ρq := by
      intro u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      rw [isOpen_iff_forall_mem_open]
      intro x0 hx0
      refine ⟨(fun y => x0 * y) '' {y | ρ₂ y w0 = w0}, ?_, isOpenMap_mul_left x0 _ (h₂ w0),
        ⟨1, by simp, by simp⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [Set.mem_ofPred_eq] at hy hx0 ⊢
      have e1 : ρq y (Submodule.Quotient.mk w0) = Submodule.Quotient.mk (ρ₂ y w0) := rfl
      rw [map_mul, Module.End.mul_apply, e1, hy, hx0]
    let gb : (V₂ ⧸ LinearMap.ker g) →ₗ[ℂ] V₃ := (LinearMap.ker g).liftQ g le_rfl
    have hgb_inj : Function.Injective gb := by
      intro a b hab
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      have hab' : g a = g b := hab
      rw [Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, hab', sub_self]
    have hgb_eq : ∀ (x : G) (u : V₂ ⧸ LinearMap.ker g), gb (ρq x u) = ρ₃ x (gb u) := by
      intro x u
      obtain ⟨w0, rfl⟩ := Submodule.Quotient.mk_surjective _ u
      exact hg x w0
    have hmem : (Submodule.Quotient.mk w : V₂ ⧸ LinearMap.ker g) ∈ GlobalTheory.PRep.twKer ρq N θ :=
      GlobalTheory.CompanionTheory.PRep.JacExact.twKer_reflect ρq ρ₃ hq h₃ N θ hθ hN gb hgb_inj hgb_eq _ hx
    rw [GlobalTheory.CompanionTheory.PRep.twKer_map_closed ρ₂ ρq N θ (LinearMap.ker g).mkQ
      (Submodule.mkQ_surjective _) (fun x v => rfl)] at hmem
    obtain ⟨w', hw', hw'eq⟩ := hmem
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq, ← hfg, LinearMap.mem_range] at hw'eq
    obtain ⟨v, hv⟩ := hw'eq
    rw [LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk (-v), ?_⟩
    simp only [GlobalTheory.BZMir.twMap, Submodule.mapQ_apply, map_neg, hv]
    rw [Submodule.Quotient.eq]
    have e2 : -(w' - w) - w = -w' := by abel
    rw [e2]
    exact Submodule.neg_mem _ hw'

end GlobalTheory.CompanionTheory.PRep.TwExact
end

section

open Zc.Comb
universe u

theorem _root_.GlobalTheory.T.shuffle_of_perm : ∀ {T : Type u} (us us' : List (List T)) (w : List T), Shuffle us w → us.Perm us' → Shuffle us' w := by
  first | exact @GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | exact GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm | (intros; apply GlobalTheory.CompanionTheory.ShuffleWords.shuffle_perm <;> assumption)
end

section

open Zc.Comb
universe u

theorem _root_.GlobalTheory.T.perm_flatten_of_shuffle : ∀ {T : Type u} (us : List (List T)) (w : List T), Shuffle us w → w.Perm us.flatten := by
  first | exact @GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | exact GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten | (intros; apply GlobalTheory.CompanionTheory.Comb.shuffle_perm_flatten <;> assumption)
end
