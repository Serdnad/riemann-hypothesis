module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem exists_pow_mul_isIntegral_of_valuation_le_one_away {F : Type} [Field F] [NumberField F] (c : 𝓞 F) (x : F)
    (h : ∀ P : HeightOneSpectrum (𝓞 F), c ∉ P.asIdeal → HeightOneSpectrum.valuation F P x ≤ 1) :
    ∃ n : ℕ, ∃ a : 𝓞 F, (c : F) ^ n * x = a := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
  have hpq' : (p : F) / q = x := hpq
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hq0' : (q : F) ≠ 0 := by exact_mod_cast hq0
  let T : Ideal (𝓞 F) := (LinearMap.range (Algebra.linearMap (𝓞 F) F)).comap
    (LinearMap.toSpanSingleton (𝓞 F) F x)
  have memT : ∀ y : 𝓞 F, y ∈ T ↔ ∃ a : 𝓞 F, (y : F) * x = a := by
    intro y
    simp only [T, Submodule.mem_comap, LinearMap.mem_range, LinearMap.toSpanSingleton_apply,
      Algebra.linearMap_apply, Algebra.smul_def]
    constructor <;> rintro ⟨a, ha⟩ <;> exact ⟨a, ha.symm⟩
  have hqT : q ∈ T := (memT q).2 ⟨p, by rw [← hpq']; field_simp⟩
  have hrad : c ∈ T.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hTP, hP⟩
    by_contra hc
    have hPne : P ≠ ⊥ := by
      intro h0
      have := hTP hqT
      rw [h0] at this
      exact hq0 (Ideal.mem_bot.1 this)
    let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPne⟩
    have hv := h v hc
    have hspan : Ideal.span {q} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hq0
    have hPunit : ¬ IsUnit P := by
      rw [Ideal.isUnit_iff]
      exact hP.ne_top
    obtain ⟨n, J, hPJ, hJ⟩ := WfDvdMonoid.max_power_factor' hspan hPunit
    rw [Ideal.dvd_iff_le] at hPJ
    obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hPJ
    have hvq : v.intValuation q ≤ WithZero.exp (-(n : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd q n).2 ⟨J, hJ⟩
    have hq' : v.intValuation q ≠ 0 := by
      rw [← v.valuation_of_algebraMap (K := F)]
      simpa using hq0'
    have hvp : v.intValuation p ≤ WithZero.exp (-(n : ℤ)) := by
      have hx : HeightOneSpectrum.valuation F v x = v.intValuation p / v.intValuation q := by
        rw [← hpq', map_div₀, v.valuation_of_algebraMap, v.valuation_of_algebraMap]
      rw [hx, div_le_one₀ (zero_lt_iff.2 hq')] at hv
      exact hv.trans hvq
    have hpn := (v.intValuation_le_pow_iff_dvd p n).1 hvp
    rw [Ideal.dvd_iff_le] at hpn
    have hps : p * s ∈ Ideal.span {q} := by
      rw [hJ]
      exact Ideal.mul_mem_mul (hpn (Ideal.mem_span_singleton_self p)) hsJ
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hps
    have hd' : (d : F) * q = p * s := by exact_mod_cast hd
    refine hsP (hTP ((memT s).2 ⟨d, ?_⟩))
    rw [← hpq']
    field_simp
    linear_combination -hd'
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨a, ha⟩ := (memT _).1 hn
  exact ⟨n, a, by push_cast at ha; exact ha⟩

theorem UpperTheory.V.ZK.Cl.cRes :
    UpperTheory.V.ZK.Cl.CRes := by
  intro L F _ _ _ _ _ k _ r
  have uniq : ∀ (x : F) (u u' : k), ResF r x u → ResF r x u' → u = u' := by
    rintro x u u' ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hx', hu'⟩
    have h1 : a * b' = a' * b := by
      have : (a : F) * b' = a' * b := by
        rw [← hx, ← hx']
        ring
      exact_mod_cast this
    have h2 := congrArg r h1
    rw [map_mul, map_mul, hu, hu'] at h2
    have h3 : (u - u') * (r b * r b') = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero hb hb')
  have base : ∀ a : 𝓞 F, ResF r (a : F) (r a) := fun a => ⟨a, 1, by simp, by simp, by simp⟩
  have arith : ∀ (x y : F) (u w : k), ResF r x u → ResF r y w →
      ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w) := by
    rintro x y u w ⟨a, b, hb, hx, hu⟩ ⟨a', b', hb', hy, hw⟩
    refine ⟨⟨a * b' + a' * b, b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩,
      ⟨a * a', b * b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩⟩
    · have e : ((a * b' + a' * b : 𝓞 F) : F) = (a : F) * b' + a' * b := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_add (f := _), map_mul, hu, hw]
      ring
    · have e : ((a * a' : 𝓞 F) : F) = (a : F) * a' := by push_cast; rfl
      have e' : ((b * b' : 𝓞 F) : F) = (b : F) * b' := by push_cast; rfl
      rw [e, e', ← hx, ← hy]
      ring
    · simp only [map_mul, hu, hw]
      ring
  have integ : ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ x : F,
      (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
        HeightOneSpectrum.valuation F P x ≤ 1) →
      (∃ n, ∃ a : 𝓞 F, algebraMap (𝓞 L) F b ^ n * x = a) ∧ ∃ u, ResF r x u := by
    intro b hb x hx
    obtain ⟨n, a, ha⟩ := exists_pow_mul_isIntegral_of_valuation_le_one_away _ x hx
    have hcast : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    refine ⟨⟨n, a, by rw [hcast]; exact ha⟩, ⟨r a / r (algebraMap (𝓞 L) (𝓞 F) b ^ n), a,
      algebraMap (𝓞 L) (𝓞 F) b ^ n, by rw [map_pow]; exact pow_ne_zero _ hb, ?_, ?_⟩⟩
    · have e : ((algebraMap (𝓞 L) (𝓞 F) b ^ n : 𝓞 F) : F)
          = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) ^ n := by push_cast; rfl
      rw [e, mul_comm]
      exact ha
    · rw [div_mul_cancel₀]
      rw [map_pow]
      exact pow_ne_zero _ hb
  refine ⟨uniq, base, arith, fun b hb => ⟨integ b hb, ?_⟩⟩
  intro α hα
  have hval : ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal →
      HeightOneSpectrum.valuation F P (α : F) = 1 := by
    intro P hP
    have h0 := hα P hP
    unfold ordP at h0
    have hne : HeightOneSpectrum.valuation F P (α : F) ≠ 0 := by simp
    rw [← WithZero.exp_log hne]
    have : (HeightOneSpectrum.valuation F P (α : F)).log = 0 := by linarith
    rw [this]
    rfl
  obtain ⟨-, u, hu⟩ := integ b hb (α : F) (fun P hP => (hval P hP).le)
  obtain ⟨-, u', hu'⟩ := integ b hb ((α⁻¹ : Fˣ) : F) (fun P hP => by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hval P hP, inv_one])
  have hmul := (arith _ _ _ _ hu hu').2
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one] at hmul
  have h1 : ResF r (1 : F) 1 := by simpa using base 1
  have huu : u * u' = 1 := uniq _ _ _ hmul h1
  exact ⟨⟨u, u', huu, by rw [mul_comm]; exact huu⟩, hu⟩
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem red_apply_map {R k : Type} [CommRing R] [Field k] (r : R →+* k) (N : ℕ) (g : GL (Fin N) R)
    (x : Fin N → R) : red r N g (r ∘ x) = r ∘ (g : Matrix (Fin N) (Fin N) R).mulVec x := by
  funext j
  simp [red, RingHom.map_mulVec]

private theorem exists_ibar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (hr : Function.Surjective r) (i : M →ₗ[R] (Fin N → R)) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) (h2 : Function.Surjective π)
    (h3 : ∀ x, π x = 0 → x ∈ RingHom.ker r • (⊤ : Submodule R M)) :
    ∃ ib : V →ₗ[k] (Fin N → k), ∀ x, ib (π x) = r ∘ i x := by
  have key : ∀ z ∈ RingHom.ker r • (⊤ : Submodule R M), r ∘ i z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      funext j
      simp [(RingHom.mem_ker).1 ha]
    · intro z w hz hw
      funext j
      have e₁ := congrFun hz j
      have e₂ := congrFun hw j
      simp only [Function.comp_apply, Pi.zero_apply] at e₁ e₂ ⊢
      rw [map_add (f := _), Pi.add_apply, map_add (f := _), e₁, e₂, add_zero]
  have wd : ∀ x y : M, π x = π y → r ∘ i x = r ∘ i y := by
    intro x y hxy
    have hz : x - y ∈ RingHom.ker r • (⊤ : Submodule R M) := h3 _ (by rw [map_sub, hxy, sub_self])
    have e := key _ hz
    funext j
    have ej := congrFun e j
    simp only [map_sub, Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at ej
    exact sub_eq_zero.1 ej
  choose pre hpre using h2
  refine ⟨{ toFun := fun v => r ∘ i (pre v), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro v w
    have e : π (pre (v + w)) = π (pre v + pre w) := by rw [map_add (f := _), hpre, hpre, hpre]
    rw [wd _ _ e, map_add (f := _)]
    funext j
    simp
  · intro c v
    obtain ⟨a, rfl⟩ := hr c
    have e : π (pre (r a • v)) = π (a • pre v) := by rw [h1, hpre, hpre]
    rw [wd _ _ e, map_smul]
    funext j
    simp
  · intro x
    exact wd _ _ (hpre _)

private theorem exists_sbar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (s : (Fin N → R) →ₗ[R] M) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) :
    ∃ sb : (Fin N → k) →ₗ[k] V, ∀ x, sb (r ∘ x) = π (s x) := by
  refine ⟨(Pi.basisFun k (Fin N)).constr k (fun j => π (s (Pi.single j 1))), fun x => ?_⟩
  rw [Module.Basis.constr_apply_fintype]
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]

  conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h1]
  simp

theorem UpperTheory.V.ZK.Cl.cFree :
    UpperTheory.V.ZK.Cl.CFree := by
  intro R _ M _ _ _ _ H _ α
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hi⟩ := Module.projective_lifting_property s LinearMap.id hs
  have hsi : ∀ y, s (i y) = y := fun y => LinearMap.congr_fun hi y
  let E : H →* Module.End R (Fin N → R) :=
    { toFun := fun h => i ∘ₗ (α h).toLinearMap ∘ₗ s + (LinearMap.id - i ∘ₗ s)
      map_one' := LinearMap.ext fun x => by simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp [hsi, map_mul, Module.End.mul_apply] }
  let lam : H →* GL (Fin N) R :=
    (Units.map (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin N → R) ≃ₐ[R] Matrix (Fin N) (Fin N) R).toMonoidHom).comp E.toHomUnits
  refine ⟨N, lam, ?_⟩
  intro k _ r hr V _ _ π μ h1 h2 h3 h4
  obtain ⟨ib, hib⟩ := exists_ibar r hr i π h1 h2 h3
  obtain ⟨sb, hsb⟩ := exists_sbar r s π h1
  have sbib : ∀ v, sb (ib v) = v := by
    intro v
    obtain ⟨x, rfl⟩ := h2 v
    rw [hib, hsb, hsi]
  let f : (V × LinearMap.ker sb) →ₗ[k] (Fin N → k) := LinearMap.coprod ib (LinearMap.ker sb).subtype
  have hfa : ∀ w : V × LinearMap.ker sb, f w = ib w.1 + (w.2 : Fin N → k) := fun w => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro w w' hww
      rw [hfa, hfa] at hww
      have e1 : w.1 = w'.1 := by
        have := congrArg sb hww
        rwa [map_add, map_add, sbib, sbib, LinearMap.mem_ker.1 w.2.2, LinearMap.mem_ker.1 w'.2.2,
          add_zero, add_zero] at this
      rw [e1] at hww
      exact Prod.ext e1 (Subtype.ext (add_left_cancel hww))
    · intro y
      refine ⟨(sb y, ⟨y - ib (sb y), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker, map_sub, sbib, sub_self]
      · rw [hfa]
        simp
  let φ := LinearEquiv.ofBijective f hf
  refine ⟨LinearMap.ker sb, φ, ?_⟩
  refine MonoidHom.ext fun h => LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Fin N → R, r ∘ x = y :=
    ⟨fun j => (hr (y j)).choose, funext fun j => (hr (y j)).choose_spec⟩
  have rhs : (cj φ) ((sumRep μ 1) h) (r ∘ x) =
      f ((μ h (φ.symm (r ∘ x)).1, (φ.symm (r ∘ x)).2)) := rfl
  have hfw : f (φ.symm (r ∘ x)) = r ∘ x := φ.apply_symm_apply (r ∘ x)
  simp only [MonoidHom.comp_apply]
  rw [rhs]
  obtain ⟨w, hw⟩ : ∃ w, φ.symm (r ∘ x) = w := ⟨_, rfl⟩
  rw [hw] at hfw ⊢
  have hyw : r ∘ x = ib w.1 + (w.2 : Fin N → k) := by
    rw [← hfa]
    exact hfw.symm
  have hv : π (s x) = w.1 := by
    rw [← hsb, hyw, map_add (f := _), sbib, LinearMap.mem_ker.1 w.2.2, add_zero]
  rw [red_apply_map]
  have hlam : ((lam h : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x = E h x := by
    show (LinearMap.toMatrix' (E h)).mulVec x = E h x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hlam]
  have e1 : E h x = i (α h (s x)) + (x - i (s x)) := rfl
  have e2 : ∀ a b : Fin N → R, r ∘ (a + (x - b)) = r ∘ a + (r ∘ x - r ∘ b) := by
    intro a b
    funext j
    simp
  rw [e1, e2, ← hib, ← hib, h4, hv, hfa, hyw]
  abel
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem dualFam (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] :
    ∃ (n : ℕ) (e f : Fin n → 𝓞 F) (b : 𝓞 L), b ≠ 0 ∧ ∀ x : F,
      algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i := by
  classical
  let B := Module.finBasis L F
  obtain ⟨m, hm, hi⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image B ∪ Finset.univ.image B.traceDual)
  refine ⟨_, fun i => ⟨m • B.traceDual i, hi _ (by simp)⟩, fun i => ⟨m • B i, hi _ (by simp)⟩,
    (m : 𝓞 L) ^ 2, pow_ne_zero _ (Int.cast_ne_zero.2 hm), fun x => ?_⟩
  have h := B.traceDual.sum_repr x
  conv_lhs => rw [← h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply, Algebra.smul_def]
  change _ = algebraMap L F (Algebra.trace L F (x * (m • B i))) * (m • B.traceDual i)
  rw [mul_smul_comm m x, map_zsmul, map_zsmul]
  simp only [zsmul_eq_mul, map_pow, map_intCast]
  ring

private theorem orth {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [IsGalois L F]
    {n : ℕ} (e f : Fin n → F) (b : L)
    (h : ∀ x : F, algebraMap L F b * x = ∑ i, algebraMap L F (Algebra.trace L F (x * f i)) * e i)
    (σ τ : F ≃ₐ[L] F) [Decidable (τ = σ)] : ∑ i, τ (f i) * σ (e i) = if τ = σ then algebraMap L F b else 0 := by
  classical
  have hli := (linearIndependent_monoidHom F F).comp (fun ρ : F ≃ₐ[L] F => (ρ : F →* F))
    (fun ρ ρ' hh => AlgEquiv.ext fun x => DFunLike.congr_fun hh x)
  have := (Fintype.linearIndependent_iffₛ.1 hli) (fun ρ => ∑ i, ρ (f i) * σ (e i))
    (fun ρ => if ρ = σ then algebraMap L F b else 0) (by
      funext x
      have h1 := congrArg σ (h x)

      simp only [map_mul, map_sum, AlgEquiv.commutes] at h1
      simp only [trace_eq_sum_automorphisms, map_mul, Finset.sum_mul] at h1
      rw [Finset.sum_comm] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, MonoidHom.coe_coe, Finset.sum_mul]
      rw [h1]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring) τ
  convert this

theorem UpperTheory.V.ZK.Cl.cSplit :
    UpperTheory.V.ZK.Cl.CSplit := by
  classical
  intro L F _ _ _ _ _ hG
  obtain ⟨n, e, f, b, hb, h⟩ := dualFam L F
  refine ⟨b, hb, fun k _ _ r hr hrb => ⟨fun v => ?_, fun a ha => ?_⟩⟩
  · choose s hs using hr
    have hs' : ∀ y, r (algebraMap (𝓞 L) (𝓞 F) (s y)) = y := hs
    have hσ : ∀ (σ : F ≃ₐ[L] F) (c : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) c) = algebraMap (𝓞 L) (𝓞 F) c :=
      fun σ c => RingOfIntegers.ext (σ.commutes (c : L))
    have ho : ∀ σ τ : F ≃ₐ[L] F, ∑ i, actO τ (f i) * actO σ (e i) =
        if τ = σ then algebraMap (𝓞 L) (𝓞 F) b else 0 := by
      intro σ τ
      apply RingOfIntegers.ext
      have := orth (fun i => (e i : F)) (fun i => (f i : F)) (b : L) h σ τ

      simp only [map_sum, map_mul]
      refine this.trans ?_
      split_ifs
      · rfl
      · simp
    refine ⟨∑ i, algebraMap (𝓞 L) (𝓞 F)
      (s (∑ τ, (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹ * v τ * r (actO τ (f i)))) * e i, fun σ => ?_⟩

    simp only [map_sum, map_mul, hσ, hs', Finset.sum_mul]
    rw [Finset.sum_comm]

    simp only [mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, ho]
    simp only [apply_ite r, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    field_simp
  · let c : Fin n → 𝓞 L := fun i => ⟨Algebra.trace L F (a * f i),
      Algebra.isIntegral_trace (R := ℤ) (a * f i).isIntegral_coe⟩
    have hc : ∀ i, algebraMap (𝓞 L) (𝓞 F) (c i) = ∑ σ : F ≃ₐ[L] F, actO σ a * actO σ (f i) := by
      intro i
      apply RingOfIntegers.ext
      have := trace_eq_sum_automorphisms (K := L) ((a : F) * f i)

      simp only [map_sum, map_mul] at this ⊢
      exact this
    have hba : algebraMap (𝓞 L) (𝓞 F) b * a = ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      apply RingOfIntegers.ext

      simp only [map_sum, map_mul]
      exact h a
    obtain ⟨b', hb'⟩ := hr (r (algebraMap (𝓞 L) (𝓞 F) b))⁻¹
    have h1 : a = algebraMap (𝓞 L) (𝓞 F) (1 - b' * b) * a +
        algebraMap (𝓞 L) (𝓞 F) b' * ∑ i, algebraMap (𝓞 L) (𝓞 F) (c i) * e i := by
      rw [← hba, map_sub, map_mul, map_one]; ring
    rw [h1]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)))
    · rw [RingHom.mem_ker, map_sub, map_mul, map_one, hb', RingHom.comp_apply, inv_mul_cancel₀ hrb, sub_self]
    · rw [RingHom.mem_ker, RingHom.comp_apply, hc]
      simp [ha]
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cSupp :
    UpperTheory.V.ZK.Cl.CSupp := by
  intro L F _ _ _ _ _ 𝔡 b₀ hb₀
  refine ⟨b₀ * ∏ P ∈ 𝔡.support, ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 L), ?_, dvd_mul_right _ _, ?_⟩
  · refine mul_ne_zero hb₀ (Finset.prod_ne_zero_iff.mpr fun P _ => ?_)
    have h : Ideal.absNorm P.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
    exact_mod_cast h
  · intro P hP
    rw [map_mul, map_prod]
    apply Ideal.mul_mem_left
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
      (fun Q : HeightOneSpectrum (𝓞 F) =>
        algebraMap (𝓞 L) (𝓞 F) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 L))
      (Finsupp.mem_support_iff.mpr hP)
    rw [hc]
    apply Ideal.mul_mem_right
    rw [map_natCast]
    exact Ideal.absNorm_mem P.asIdeal
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cTriv :
    UpperTheory.V.ZK.Cl.CTriv := by
  intro k _ A _ m θ hθ H V P U
  intro _ _ _ _ _ _ _ _ _ _ μ φ z hz
  obtain ⟨-, hnat, hcomp, -, hsub⟩ := sChain A
  have cyc : ∀ {G G' : Type} [Group G] [Group G'] (f : G →* G') (w : Ch A G (m + 1)),
      Cyc w → Cyc (cm A f (m + 1) w) := by
    intro G G' _ _ f w hw
    unfold Cyc at hw ⊢
    rw [hnat, hw, map_zero]
  rw [hcomp, hθ.iso (V × P) U φ _ (cyc _ _ hz), hθ.add H V P μ 1 z hz]
  have htriv : (θ P) (cm A (1 : H →* P ≃ₗ[k] P) (m + 1) z) = 0 := by
    apply hθ.bdry
    have hf : (1 : H →* P ≃ₗ[k] P) = (1 : Unit →* P ≃ₗ[k] P).comp (1 : H →* Unit) := by
      ext h x
      rfl
    rw [hf, hcomp]
    obtain ⟨w, hw⟩ := hsub Unit m _ (cyc (1 : H →* Unit) z hz)
    rw [← hw, ← hnat]
    exact ⟨_, rfl⟩
  rw [htriv, add_zero]
end
