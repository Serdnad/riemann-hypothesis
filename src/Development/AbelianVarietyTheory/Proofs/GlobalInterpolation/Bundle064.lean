module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValuedAlgebraMapLtOneIff
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle010
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle002
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle061
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.RootSplitting

section General

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

theorem one_tmul_injective {a b : K} (h : (1 : E) ⊗ₜ[F] a = (1 : E) ⊗ₜ[F] b) : a = b :=
  Algebra.TensorProduct.includeRight_injective (R := F) (A := E) (B := K)
    (algebraMap F E).injective h

theorem algebraMap_tmul (t : F) :
    (algebraMap F E t) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (algebraMap F K t) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_basis (hdeg : Module.finrank F E = 2) (θ : E) (hθ : θ ∉ (algebraMap F E).range) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = θ := by
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    intro a ha
    exact hθ ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdeg]), ?_, ?_⟩ <;> simp

theorem exists_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ) (x : E) :
    ∃ p q : F, x = p • (1 : E) + q • θ :=
  ⟨b.repr x 0, b.repr x 1, by
    have := b.sum_repr x
    rw [Fin.sum_univ_two, h0, h1] at this
    exact this.symm⟩

theorem exists_algHom (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (t n : F) (hθ : θ * θ = (-n) • (1 : E) + t • θ) (r : K) (hr : r * r = (-n) • (1 : K) + t • r) :
    ∃ φ : E →ₐ[F] K, φ θ = r := by
  let f : E →ₗ[F] K := b.constr F ![1, r]
  have f0 : f 1 = 1 := by rw [← h0]; simp [f]
  have f1 : f θ = r := by rw [← h1]; simp [f]
  refine ⟨AlgHom.ofLinearMap f f0 fun x y => ?_, f1⟩
  obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 x
  obtain ⟨p', q', rfl⟩ := exists_coord b h0 h1 y
  simp only [mul_add, add_mul, smul_mul_smul_comm, one_mul, mul_one, hθ, hr, map_add (f := _), map_smul,
    f0, f1]

theorem exists_tensor_coord (b : Module.Basis (Fin 2) F E) {θ : E} (h0 : b 0 = 1) (h1 : b 1 = θ)
    (x : E ⊗[F] K) : ∃ a c : K, x = (1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul e k =>
    obtain ⟨p, q, rfl⟩ := exists_coord b h0 h1 e
    exact ⟨p • k, q • k, by rw [TensorProduct.add_tmul, TensorProduct.smul_tmul,
      TensorProduct.smul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, c, rfl⟩ := hx
    obtain ⟨a', c', rfl⟩ := hy
    exact ⟨a + a', c + c', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

theorem exists_ringEquiv (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (θ : E) (r r' : K) (hne : r - r' ≠ 0)
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : K) = (1 : E) ⊗ₜ[F] (r * r')) :
    ∃ (s : E ⊗[F] K ≃+* K × K) (φ : E →ₐ[F] K), φ θ = r ∧ φ (σ θ) = r' ∧
      ∀ (e : E) (k : K), s (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := by
  obtain ⟨t, ht'⟩ := hfix (θ + σ θ) (by rw [map_add (f := _), hσ, add_comm])
  obtain ⟨n, hn'⟩ := hfix (θ * σ θ) (by rw [map_mul, hσ, mul_comm])
  have htK : algebraMap F K t = r + r' := by
    rw [← ht', algebraMap_tmul] at ht; exact one_tmul_injective ht
  have hnK : algebraMap F K n = r * r' := by
    rw [← hn', algebraMap_tmul] at hn; exact one_tmul_injective hn
  have hθ : θ ∉ (algebraMap F E).range := by
    rintro ⟨a, rfl⟩
    rw [AlgHom.commutes, ← map_add (f := _)] at ht'
    rw [AlgHom.commutes, ← map_mul] at hn'
    obtain rfl := (algebraMap F E).injective ht'
    obtain rfl := (algebraMap F E).injective hn'
    rw [map_add (f := _)] at htK
    rw [map_mul] at hnK
    apply hne
    have : (r - r') ^ 2 = 0 := by
      linear_combination (-(r + r' + 2 * algebraMap F K a)) * htK + 4 * hnK
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  obtain ⟨b, h0, h1⟩ := exists_basis hdeg θ hθ
  obtain ⟨φ, hφ⟩ := exists_algHom b h0 h1 t n
    (by simp only [Algebra.smul_def, map_neg, ht', hn']; ring) r
    (by simp only [Algebra.smul_def, map_neg, htK, hnK]; ring)
  have hφ' : φ (σ θ) = r' := by
    have := congrArg φ ht'
    rw [AlgHom.commutes, map_add (f := _), hφ, htK] at this
    exact (add_left_cancel this).symm
  let g : E ⊗[F] K →ₐ[F] K × K :=
    (Algebra.TensorProduct.lift φ (AlgHom.id F K) fun _ _ => Commute.all _ _).prod
      (Algebra.TensorProduct.lift (φ.comp σ) (AlgHom.id F K) fun _ _ => Commute.all _ _)
  have hg : ∀ (e : E) (k : K), g (e ⊗ₜ[F] k) = (φ e * k, φ (σ e) * k) := fun e k => rfl
  have hg2 : ∀ a c : K, g ((1 : E) ⊗ₜ[F] a + θ ⊗ₜ[F] c) = (a + r * c, a + r' * c) := by
    intro a c
    rw [map_add (f := _), hg, hg, hφ, hφ']; simp
  refine ⟨RingEquiv.ofBijective g ⟨?_, ?_⟩, φ, hφ, hφ', hg⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, c, rfl⟩ := exists_tensor_coord b h0 h1 x
    rw [hg2, Prod.mk_eq_zero] at hx
    have hc : c = 0 := by
      have : (r - r') * c = 0 := by linear_combination hx.1 - hx.2
      exact (mul_eq_zero.1 this).resolve_left hne
    have ha : a = 0 := by simpa [hc] using hx.1
    simp [ha, hc]
  · rintro ⟨a, c⟩
    refine ⟨(1 : E) ⊗ₜ[F] (c - r' * ((a - c) / (r - r'))) + θ ⊗ₜ[F] ((a - c) / (r - r')), ?_⟩
    rw [hg2]
    congr 1
    · field_simp; ring
    · ring

end General

theorem exists_isSplitting (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F)) (θ : E)
    (r r' : v.adicCompletionIntegers F) (hθ : IsIntegral ℤ θ) (hu : IsUnit (r - r'))
    (ht : (θ + σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) + r'))
    (hn : (θ * σ θ) ⊗ₜ[F] (1 : v.adicCompletion F) =
      (1 : E) ⊗ₜ[F] ((r : v.adicCompletion F) * r')) :
    ∃ s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      IsSplitting σ v s ∧
      s (θ ⊗ₜ[F] (1 : v.adicCompletion F)) =
        ((r : v.adicCompletion F), (r' : v.adicCompletion F)) := by
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  have huK : ((r : v.adicCompletion F) - r') * u = 1 := by exact_mod_cast congrArg Subtype.val hu'
  have hne : (r : v.adicCompletion F) - r' ≠ 0 := left_ne_zero_of_mul_eq_one huK
  obtain ⟨s, φ, h1, h2, hs⟩ := exists_ringEquiv σ hdeg hσ hfix θ _ _ hne ht hn
  have hint : ∀ x : E, IsIntegral ℤ x → φ x ∈ v.adicCompletionIntegers F := by
    intro x hx
    obtain ⟨p, hp, hp0⟩ := map_isIntegral_int φ hx
    have h4 : IsIntegral (v.adicCompletionIntegers F) (φ x) :=
      ⟨p.map (Int.castRingHom _), hp.map _, by
        rw [Polynomial.eval₂_map]
        exact (congrArg (fun f => Polynomial.eval₂ f (φ x) p) (RingHom.ext_int _ _)).trans hp0⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h4
    exact hy ▸ y.2
  have hone : ∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a; rw [hs]; simp
  refine ⟨s, ⟨hone, fun x => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, by rw [hs, h1, h2]; simp⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e k =>
      have : sigR σ (v.adicCompletion F) (e ⊗ₜ[F] k) = σ e ⊗ₜ[F] k := rfl
      rw [this, hs, hs, hσ]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩
      · simp only [hs, mul_one]
        exact ⟨hint _ a.2, hint _ (IsIntegral.map (σ : E →+* E).toIntAlgHom a.2)⟩
      · simp only [hone]; exact ⟨a.2, a.2⟩
    | zero => simp
    | one => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · have hm : ∀ a ∈ v.adicCompletionIntegers F, (1 : E) ⊗ₜ[F] a ∈ intV E v := fun a ha =>
      Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
    have hθm : θ ⊗ₜ[F] (1 : v.adicCompletion F) ∈ intV E v :=
      GlobalTheory.OverCompare.tmul_mem_intV (⟨θ, hθ⟩ : 𝓞 E)
    have hc : ((s x).1 - (s x).2) * u ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem hx.1 hx.2) u.2
    have : x = (1 : E) ⊗ₜ[F] ((s x).2 - r' * (((s x).1 - (s x).2) * u)) +
        θ ⊗ₜ[F] (1 : v.adicCompletion F) * (1 : E) ⊗ₜ[F] (((s x).1 - (s x).2) * u) := by
      apply s.injective
      rw [map_add (f := _), map_mul, hone, hone, hs, h1, h2]
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.fst_mul]
        linear_combination (-((s x).1 - (s x).2)) * huK
      · simp only [Prod.snd_add, Prod.snd_mul]; ring
    rw [this]
    exact add_mem (hm _ (sub_mem hx.2 (mul_mem r'.2 hc))) (mul_mem hθm (hm _ hc))

end GlobalTheory.RootSplitting
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverResidue

theorem nonempty_equiv_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I.IsMaximal) (T : ℕ) (hT : T.Prime) (hc : Nat.card M = T)
    (h0 : ∀ a ∈ I, ∀ m : M, a • m = 0) : Nonempty (M ≃ₗ[R] (R ⧸ I)) := by
  have : Fact T.Prime := ⟨hT⟩
  have : Finite M := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.1 (hc ▸ hT.one_lt)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m₀
  have hsur : Function.Surjective f := by
    intro m
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc hm₀ (g' := m))
    exact ⟨(n : R), by simp [f, Int.cast_smul_eq_zsmul]⟩
  have hker : I = LinearMap.ker f := by
    refine hI.eq_of_le ?_ fun a ha => h0 a ha m₀
    rw [Ideal.ne_top_iff_one]
    simpa [f] using hm₀
  subst hker
  exact ⟨(f.quotKerEquivOfSurjective hsur).symm⟩

theorem exists_addEquiv_field {R M k : Type} [CommRing R] [AddCommGroup M] [Module R M] [Field k]
    (ρ : R →+* k) (hρ : Function.Surjective ρ) (e : M ≃ₗ[R] (R ⧸ RingHom.ker ρ)) :
    ∃ ε : M ≃+ k, ∀ (a : R) (m : M), ε (a • m) = ρ a * ε m := by
  refine ⟨e.toAddEquiv.trans (RingHom.quotientKerEquivOfSurjective hρ).toAddEquiv, fun a m => ?_⟩
  show RingHom.quotientKerEquivOfSurjective hρ (e (a • m)) =
      ρ a * RingHom.quotientKerEquivOfSurjective hρ (e m)
  rw [map_smul, Algebra.smul_def, map_mul]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_red (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, p x ∈ v.adicCompletionIntegers F)
    (hsur : ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, p x = a) :
    ∃ ρ : intV E v →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F),
      Function.Surjective ρ ∧ primeOf p = RingHom.ker ρ ∧
      (∀ a : intV E v, a ∈ RingHom.ker ρ ↔ Valued.v (p a) < 1) ∧
      ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = p a →
        ρ a = IsLocalRing.residue _ a' := by
  let q : intV E v →+* v.adicCompletionIntegers F :=
    (p.comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) fun x => hp x x.2
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hsur a a.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hk : ∀ a : intV E v, a ∈ RingHom.ker ((IsLocalRing.residue _).comp q) ↔
      Valued.v (p a) < 1 := by
    intro a
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := q a)
  refine ⟨(IsLocalRing.residue _).comp q, IsLocalRing.residue_surjective.comp hq, ?_, hk, ?_⟩
  · apply le_antisymm
    · rw [primeOf, Ideal.span_le]
      exact fun a ha => (hk a).2 ha
    · exact fun a ha => Ideal.subset_span ((hk a).1 ha)
  · intro a a' h
    have : q a = a' := Subtype.ext h.symm
    rw [RingHom.comp_apply, this]

theorem residue_of_prime_card : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (M : Type) [AddCommGroup M] [Module (intV E v) M] (T : ℕ), T.Prime → Nat.card M = T → (∀ (a : intV E v) (m : M), Valued.v (prP s a) < 1 → a • m = 0) → (∃ ε : M ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F), ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a → ∀ m, ε (a • m) = a' • ε m) ∧ Nonempty (M ≃ₗ[intV E v] (intV E v ⧸ primeOf (prP s))) ∧ Nat.card (intV E v ⧸ primeOf (prPbar s)) = T := by
  intro F E _ _ _ _ _ σ v s hs M _ _ T hT hc h0
  obtain ⟨ρ, hρ, hρk, hρm, hρa⟩ := exists_red (prP s) (fun x hx => ((hs.2.2 x).1 hx).1)
    (GlobalTheory.OverCompare.sur_prP hs)
  obtain ⟨ρ', hρ', hρk', -, -⟩ := exists_red (prPbar s) (fun x hx => ((hs.2.2 x).1 hx).2)
    (GlobalTheory.OverCompare.sur_prPbar hs)
  rw [hρk, hρk']
  obtain ⟨e⟩ := nonempty_equiv_quot (M := M) (RingHom.ker ρ) (RingHom.ker_isMaximal_of_surjective ρ hρ)
    T hT hc fun a ha m => h0 a m ((hρm a).1 ha)
  obtain ⟨ε, hε⟩ := exists_addEquiv_field ρ hρ e
  refine ⟨⟨ε, fun a a' h m => ?_⟩, ⟨e⟩, ?_⟩
  · rw [hε, hρa a a' h]
    rfl
  · rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hρ').toEquiv, ← hc]
    exact (Nat.card_congr ε.toEquiv).symm

end GlobalTheory.OverResidue
end

section

open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.Proof.TensorMapDescent

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

section BaseChange

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem fockB_map {σ : Type} (f g : MvPolynomial σ K) : fockB (map φ f) (map φ g) = φ (fockB f g) := by

  rw [fockB_eq_sum _ _ f.support (support_map_subset _ _), fockB, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [coeff_map]

theorem map_ten {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) :
    map φ (ten f) = ten fun τ => map φ (f τ) := by
  unfold ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => fk_map_blockEmb φ τ _

theorem ten_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (f : ι → MvPolynomial (Fin n × Fin n) K)
    (hf : ∀ τ, f τ ∈ nablaSq K n (lam τ)) : ten f ∈ VV K lam :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem ten_ne_zero {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) K) (hf : ∀ τ, f τ ≠ 0) :
    ten f ≠ 0 := by
  unfold ten
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have hinj : Function.Injective (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ) :=
    MvPolynomial.rename_injective _ (fun a b h => (Prod.mk.inj h).2)
  exact (map_ne_zero_iff _ hinj).mpr (hf τ)

theorem map_mem_VV {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F : Pol K ι n) (hF : F ∈ VV K lam) :
    map φ F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := map_ten φ f
    unfold ten at h
    rw [h]
    exact ten_mem lam _ fun τ => Formalism.GradedWeylDivisibility.dualWeylMap K K' φ n n _ _ (hf τ)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem ssB_desc {n : ℕ} (ν : Fin n → ℕ) (m : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    ∃ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n ν, ssB K' ν m = map φ f := by
  obtain ⟨k, sz, hsz, I, hsh, -, h⟩ := ((Formalism.GradedWeylDivisibility.sSBasis K' n n ν).choose_spec.2 m).2.2
  refine ⟨Formalism.GradedWeylDivisibility.bideterminant K sz hsz I, ?_, by rw [fk_map_bidet]; exact h⟩
  rw [← hsh]
  exact Formalism.GradedWeylDivisibility.bidetMem K n n k sz hsz I

theorem bVVfun_desc {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (i : VVIdx lam) :
    ∃ F ∈ VV K lam, bVVfun K' lam i = map φ F := by
  choose f hf hf' using fun τ => ssB_desc φ (lam τ).natW (i τ)
  refine ⟨ten f, ten_mem lam f hf, ?_⟩
  rw [map_ten]
  exact congrArg ten (funext hf')

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem eq_zero_of_fockB [CharZero K] (sg : ι → DomWeight n) (x : VV K sg)
    (h : ∀ i, fockB (bVVfun K sg i) (x : Pol K ι n) = 0) : x = 0 := by
  refine (pairingBNondegenerate_holds K ι n sg).2 x fun y => ?_
  have : (pairBK sg).flip x = 0 := by
    refine (bVV K sg).ext fun i => ?_
    rw [LinearMap.flip_apply, pairBK_apply, pairB_apply, bVV_coe, h i, mul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun this y

open Classical in
theorem gramB_det_ne_zero [CharZero K] (sg : ι → DomWeight n) : (Br.gramB (K := K) sg).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 : ∑ j, v j • bVV K sg j = 0 := by
    refine eq_zero_of_fockB sg _ fun i => ?_
    have := congrFun hv0 i
    simp only [Matrix.mulVec, dotProduct, Br.gramB, Matrix.of_apply, Pi.zero_apply] at this

    rw [← fockBL_apply, Submodule.coe_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, map_smul, bVV_coe, fockBL_apply, smul_eq_mul, mul_comm]
  exact hv (funext (Fintype.linearIndependent_iff.mp (bVV K sg).linearIndependent v h1))

theorem fockB_projVV_basis [CharZero K] (sg : ι → DomWeight n) (F : Pol K ι n) (k : VVIdx sg) :
    fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) = fockB (bVVfun K sg k) F := by
  classical
  have hG := Matrix.mul_nonsing_inv (Br.gramB (K := K) sg) (Ne.isUnit (gramB_det_ne_zero sg))
  have h1 : fockB (bVVfun K sg k) (Br.projVV sg F : Pol K ι n) =
      ∑ i, ∑ j, Br.gramB (K := K) sg k i * (Br.gramB (K := K) sg)⁻¹ i j * fockB (bVVfun K sg j) F := by
    rw [← fockBL_apply]

    simp only [Br.projVV, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Submodule.coe_sum,
    Submodule.coe_smul, map_sum, map_smul, bVV_coe, fockBL_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show Br.gramB (K := K) sg k i = fockB (bVVfun K sg k) (bVVfun K sg i) from rfl]
    ring
  rw [h1, Finset.sum_comm]
  simp only [← Finset.sum_mul, ← Matrix.mul_apply, hG, Matrix.one_apply]
  simp

theorem fockB_projVV [CharZero K] (sg : ι → DomWeight n) (F y : Pol K ι n) (hy : y ∈ VV K sg) :
    fockB y (Br.projVV sg F : Pol K ι n) = fockB y F := by
  rw [← (bVVfun_spec K sg).2] at hy
  simp only [← fockBL_apply]
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact fockB_projVV_basis sg F k
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
  | smul c x _ hx => simp only [map_smul, LinearMap.smul_apply, hx]

theorem projVV_map [CharZero K] [CharZero K'] (sg : ι → DomWeight n) (F : Pol K ι n) :
    (Br.projVV sg (map φ F) : Pol K' ι n) = map φ (Br.projVV sg F : Pol K ι n) := by
  have h := eq_zero_of_fockB sg
    (Br.projVV sg (map φ F) - ⟨map φ (Br.projVV sg F : Pol K ι n), map_mem_VV φ sg _ (Br.projVV sg F).2⟩) fun i => by
      rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply, fockB_projVV_basis]
      obtain ⟨Y, hY, hY'⟩ := bVVfun_desc φ sg i
      rw [hY', fockB_map, fockB_map, fockB_projVV sg F Y hY, sub_self]
  exact congrArg Subtype.val (sub_eq_zero.mp h)

variable {N : ℕ} (hN : N = n + 1)

omit [Fintype ι] in
theorem coefLast_map (b : ι → Fin n → ℕ) (F : Pol K ι N) :
    Br.coefLast hN b (map φ F) = map φ (Br.coefLast hN b F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have h1 : (monomial m a : Pol K ι N) = a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    have h2 : (monomial m (φ a) : Pol K' ι N) = φ a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [map_monomial, h2, h1, map_smul, map_smul, Br.coefLast_monomial, Br.coefLast_monomial]
    split_ifs
    · simp [smul_monomial, map_monomial]
    · simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem xiBr_map (lam : DomWeight N) (sg : DomWeight n) : map φ (Br.xiBr K hN lam sg) = Br.xiBr K' hN lam sg := by
  simp only [Br.xiBr, Br.zMinor, map_prod, map_mul, map_pow, fk_map_initMinor, Formalism.GradedWeylDivisibility.lclosedeq_lpMinor_map]

theorem brConst_map (lam : ι → DomWeight N) (sg : ι → DomWeight n) :
    φ (Br.brConst hN K lam sg) = Br.brConst hN K' lam sg := by
  simp only [Br.brConst, Br.kapBr, map_prod, map_mul, map_div₀, map_intCast, ← fockB_map, xiBr_map, extremal,
    Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

theorem branchingProjection_map [CharZero K] [CharZero K'] (lam : ι → DomWeight N) (sg : ι → DomWeight n) (F : Pol K ι N) :
    (Br.brStdP hN lam sg (map φ F) : Pol K' ι n) = map φ (Br.brStdP hN lam sg F : Pol K ι n) := by
  simp only [Br.brStdP, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.coe_smul]
  rw [coefLast_map, projVV_map, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, map_C, brConst_map]

theorem brOne_map [CharZero K] [CharZero K'] (lam : DomWeight N) (sg : DomWeight n) (f : MvPolynomial (Fin N × Fin N) K) :
    GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K' hN lam sg (map φ f) = map φ (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne K hN lam sg f) := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Submodule.subtype_apply]
  rw [← map_rename, branchingProjection_map, map_rename]

end BaseChange

end GlobalTheory.Proof.TensorMapDescent
end
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.weakApproximation_unitaryLattices_splitPrime : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → letI := D.host.cmStar; ∃ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' M M' ∧ EqAt D p (StandardLatticesGL3.stdL D N) M ∧ EqAt D p (StandardLatticesGL3.stdL D N') M' ∧ L = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M ∧ L' = SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M' := by
  first | exact @GlobalTheory.MomN.weakApprox_split | exact GlobalTheory.MomN.weakApprox_split | (intros; apply GlobalTheory.MomN.weakApprox_split <;> assumption)
end
