module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle166
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle164
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle095
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle094
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle093
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle062
public import GroundTheory.LocalFields.Bundle001
public import GroundTheory.LocalFields.UnitsPowers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle163
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003

@[expose] public section

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.PairClass

theorem exists_aeval_eq_of_separable {F A : Type} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (y : A) :
    ∃ q : F[X], y = aeval a q := by
  obtain ⟨w, hw⟩ := Formalism.IrreducibleCountingLemmas.Z.base_change_cyclic_vector F A (LinearMap.mulLeft F a) hs
  have key : ∀ (p : F[X]) (z : A), aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
    intro p z
    have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
      aeval_algHom_apply (Algebra.lmul F A) a p
    have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
    rw [← h2, h1]
    rfl
  obtain ⟨p1, hp1⟩ := hw 1
  obtain ⟨p2, hp2⟩ := hw (w * w)
  obtain ⟨p3, hp3⟩ := hw y
  rw [key] at hp1 hp2 hp3
  have hw2 : w = aeval a p2 := by
    calc w = w * w * aeval a p1 := by rw [mul_assoc, mul_comm w (aeval a p1), hp1, mul_one]
      _ = aeval a p2 * (aeval a p1 * w) := by rw [← hp2]; ring
      _ = aeval a p2 := by rw [hp1, mul_one]
  exact ⟨p3 * p2, by rw [← hp3, map_mul, hw2]⟩

theorem aeval_mulLeft_apply {F A : Type} [Field F] [CommRing A] [Algebra F A] (a : A) (p : F[X]) (z : A) :
    aeval (LinearMap.mulLeft F a) p z = aeval a p * z := by
  have h1 : aeval (Algebra.lmul F A a) p = Algebra.lmul F A (aeval a p) :=
    aeval_algHom_apply (Algebra.lmul F A) a p
  have h2 : Algebra.lmul F A a = LinearMap.mulLeft F a := rfl
  rw [← h2, h1]
  rfl

theorem trace_nondeg (F A : Type) [Field F] [CharZero F] [CommRing A] [Algebra F A] [Module.Finite F A]
    (a : A) (hs : (LinearMap.mulLeft F a).charpoly.Separable) (x : A)
    (hx : ∀ y, Algebra.trace F A (x * y) = 0) : x = 0 := by
  classical
  let b := Module.finBasis F A
  have hM : IsNilpotent (Algebra.leftMulMatrix b x) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [pow_succ', hx]
  obtain ⟨k, hk⟩ := hM
  have hxk : x ^ k = 0 := by
    rw [← map_pow] at hk
    exact Algebra.leftMulMatrix_injective b (by rw [hk, map_zero])
  obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable a hs x
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (LinearMap.mulLeft F a) hs _ dvd_rfl
  have h1 : (LinearMap.mulLeft F a).charpoly ∣ q ^ (k + 1) :=
    he _ (by rw [aeval_mulLeft_apply, map_pow, pow_succ, hxk, zero_mul, zero_mul])
  obtain ⟨r, hr⟩ := (Squarefree.dvd_pow_iff_dvd hs.squarefree (Nat.succ_ne_zero k)).1 h1
  have h3 : aeval (LinearMap.mulLeft F a) q = 0 := by
    rw [hr, map_mul, LinearMap.aeval_self_charpoly, zero_mul]
  have h4 := LinearMap.congr_fun h3 1
  rwa [aeval_mulLeft_apply, mul_one] at h4

theorem trace_σ (K : UQ) (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  apply GlobalTheory.SesqAsym.trace_σ <;> assumption

theorem exists_degreeLT_equiv (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] V) (P : F[X]) (hP : f.charpoly = P) (hs : P.Separable) :
    ∃ (e₀ : V) (ψ : degreeLT F P.natDegree ≃ₗ[F] V), ∀ p, ψ p = aeval f (p : F[X]) e₀ := by
  subst hP
  obtain ⟨e₀, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq f hs f.charpoly dvd_rfl
  let ψ : degreeLT F f.charpoly.natDegree →ₗ[F] V :=
    ((LinearMap.applyₗ e₀) ∘ₗ (aeval f).toLinearMap) ∘ₗ (degreeLT F _).subtype
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    have h1 : f.charpoly ∣ (q : F[X]) := he _ hq
    have h2 : (q : F[X]).degree < f.charpoly.degree := by
      rw [degree_eq_natDegree f.charpoly_monic.ne_zero]
      exact mem_degreeLT.1 q.2
    exact Subtype.ext (eq_zero_of_dvd_of_degree_lt h1 h2)
  have : FiniteDimensional F (degreeLT F f.charpoly.natDegree) :=
    (degreeLTEquiv F _).symm.finiteDimensional
  have hdim : Module.finrank F (degreeLT F f.charpoly.natDegree) = Module.finrank F V := by
    rw [(degreeLTEquiv F _).finrank_eq, Module.finrank_fin_fun, LinearMap.charpoly_natDegree]
  exact ⟨e₀, LinearMap.linearEquivOfInjective ψ hinj hdim, fun p => rfl⟩

theorem exists_intertwine (F V W : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W] (f : V →ₗ[F] V) (g : W →ₗ[F] W)
    (hs : f.charpoly.Separable) (he : f.charpoly = g.charpoly) : ∃ e : V ≃ₗ[F] W, ∀ v, e (f v) = g (e v) := by
  set P := f.charpoly with hPdef
  have hP : P.Monic := f.charpoly_monic
  obtain ⟨e₁, ψ₁, hψ₁⟩ := exists_degreeLT_equiv F V f P rfl hs
  obtain ⟨e₂, ψ₂, hψ₂⟩ := exists_degreeLT_equiv F W g P he.symm hs
  refine ⟨ψ₁.symm.trans ψ₂, fun v => ?_⟩
  obtain ⟨p, rfl⟩ := ψ₁.surjective v
  have hm : (X * (p : F[X])) %ₘ P ∈ degreeLT F P.natDegree := by
    rw [mem_degreeLT, ← degree_eq_natDegree hP.ne_zero]
    exact degree_modByMonic_lt _ hP
  have h1 : f (ψ₁ p) = ψ₁ ⟨_, hm⟩ := by
    rw [hψ₁, hψ₁, aeval_modByMonic_eq_self_of_root (LinearMap.aeval_self_charpoly f), map_mul, aeval_X,
      Module.End.mul_apply]
  have h2 : ψ₂ ⟨_, hm⟩ = g (ψ₂ p) := by
    rw [hψ₂, hψ₂, aeval_modByMonic_eq_self_of_root (show aeval g P = 0 by rw [he]; exact LinearMap.aeval_self_charpoly g),
      map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h2, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

theorem exists_herm_model : ∀ (K : UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V] [Module.Finite K.E V] (h : V → V → K.E), (∀ x y z, h (x + y) z = h x z + h y z) → (∀ (c : K.E) x z, h (c • x) z = c * h x z) → (∀ x y, h y x = K.c (h x y)) → (∀ y, (∀ z, h y z = 0) → y = 0) → ∀ (B : InvAlg K) (g : V →ₗ[K.E] V), B.P.Separable → g.charpoly = B.P → ((B.g * B.σ B.g = 1 ∧ ∀ y z, h (g y) (g z) = h y z) ∨ (B.σ B.g = B.g ∧ ∀ y z, h (g y) z = h y (g z))) → ∃ (x : B.Aˣ) (e : B.A ≃ₗ[K.E] V), B.σ (x : B.A) = x ∧ (∀ y, e (B.g * y) = g (e y)) ∧ ∀ y z, h (e y) (e z) = B.herm x y z := by
  intro K V _ _ _ _ _ h hadd hsm hherm hnd B g hsep hchar hcase
  have hsep' : (LinearMap.mulLeft K.E B.g).charpoly.Separable := hsep
  obtain ⟨e, he⟩ := exists_intertwine K.E B.A V (LinearMap.mulLeft K.E B.g) g hsep hchar.symm
  have he' : ∀ y, e (B.g * y) = g (e y) := fun y => he y
  have hadd2 : ∀ x y z, h x (y + z) = h x y + h x z := by
    intro x y z
    rw [hherm (y + z) x, hadd, map_add (f := _), ← hherm y x, ← hherm z x]
  have hsm2 : ∀ (c : K.E) x z, h x (c • z) = K.c c * h x z := by
    intro c x z
    rw [hherm (c • z) x, hsm, map_mul, ← hherm z x]
  let S : B.A → Prop := fun a => ∀ y z, h (e (a * y)) (e z) = h (e y) (e (B.σ a * z))
  have Salg : ∀ c : K.E, S (algebraMap K.E B.A c) := by
    intro c y z
    rw [B.σ_alg, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul, hsm, hsm2, K.c_c]
  have Sg : S B.g := by
    intro y z
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hz : z = B.g * (B.σ B.g * z) := by rw [← mul_assoc, h1, one_mul]
      conv_lhs => rw [hz]
      rw [he', he', h2]
    · rw [h1, he', he', h2]
  have Sadd : ∀ a b, S a → S b → S (a + b) := by
    intro a b ha hb y z
    rw [add_mul, map_add (f := _), hadd, ha, hb, map_add (f := _), add_mul, map_add (f := _), hadd2]
  have Smul : ∀ a b, S a → S b → S (a * b) := by
    intro a b ha hb y z
    rw [mul_assoc, ha, hb, show B.σ b * (B.σ a * z) = B.σ (a * b) * z by rw [map_mul B.σ]; ring]
  have Spoly : ∀ q : K.E[X], S (aeval B.g q) := by
    intro q
    induction q using Polynomial.induction_on with
    | C c => rw [aeval_C]; exact Salg c
    | add p q hp hq => rw [map_add (f := _)]; exact Sadd _ _ hp hq
    | monomial n c ih =>
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]; exact Smul _ _ ih Sg
  have Sall : ∀ a, S a := by
    intro a
    obtain ⟨q, rfl⟩ := exists_aeval_eq_of_separable B.g hsep' a
    exact Spoly q

  let φ : Module.Dual K.E B.A :=
    { toFun := fun y => h (e y) (e 1)
      map_add' := fun y z => by rw [map_add (f := _), hadd]
      map_smul' := fun c y => by rw [map_smul, hsm]; rfl }
  have hinj : Function.Injective (Algebra.traceForm K.E B.A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact trace_nondeg K.E B.A B.g hsep' x fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this
  have hsurj : Function.Surjective (Algebra.traceForm K.E B.A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨x, hx⟩ := hsurj φ
  have hxy : ∀ y, Algebra.trace K.E B.A (x * y) = h (e y) (e 1) := fun y => by
    rw [← Algebra.traceForm_apply, hx]; rfl
  have hrep : ∀ y z, h (e y) (e z) = Algebra.trace K.E B.A (x * y * B.σ z) := by
    intro y z
    have := Sall (B.σ z) y 1
    rw [B.σ_σ, mul_one] at this
    rw [← this, ← hxy]
    congr 1
    ring
  have hfix : B.σ x = x := by
    have h0 := trace_nondeg K.E B.A B.g hsep' (B.σ x - x) fun y => by
      have h1 : Algebra.trace K.E B.A (B.σ x * y) = K.c (Algebra.trace K.E B.A (x * B.σ y)) := by
        rw [← trace_σ, map_mul B.σ x (B.σ y), B.σ_σ]
      have h2 : Algebra.trace K.E B.A (x * B.σ y) = h (e 1) (e y) := by
        rw [hrep]; ring_nf
      rw [sub_mul, map_sub, h1, h2, hherm (e y) (e 1), K.c_c, hxy, sub_self]
    exact sub_eq_zero.1 h0
  have hunit : IsUnit x := by
    have hi : Function.Injective (LinearMap.mulLeft K.E x) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hy' : x * y = 0 := hy
      apply e.injective
      rw [map_zero]
      apply hnd
      intro v
      rw [← e.apply_symm_apply v, hrep, hy', zero_mul, map_zero]
    obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hi) 1
    exact IsUnit.of_mul_eq_one y hy
  exact ⟨hunit.unit, e, hfix, he', fun y z => hrep y z⟩

end GlobalTheory.UnitLemma.PairClass
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.VirtualTrace

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def listSum (h : IsPlaceOver A w) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  L.foldr (fun x s => WD.std (x.2.sum s.2)) ⟨0, WDRep.diag h (ι := Fin 0) fun i => i.elim0⟩

theorem mk_listSum_cons (x : Σ n : ℕ, WDRep h (Fin n → ℂ)) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    WD.mk (listSum h (x :: L)).2 = WD.lpSum (WD.mk x.2) (WD.mk (listSum h L).2) := by
  rw [WD.lpSum_mk]
  exact WD.sound (WD.iso_std _).symm

theorem trace_std {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _

theorem trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']

theorem map_lpZero {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) : f (WD.lpZero (h := h)) = 1 := by
  have hzero := hf (WD.lpZero (h := h)) (WD.lpZero (h := h))
  rw [WD.lpSum_zero] at hzero
  exact mul_left_cancel (hzero.symm.trans (mul_one _).symm)

theorem map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by
  induction L with
  | nil => exact map_lpZero f hf
  | cons x L ih => rw [mk_listSum_cons, hf, ih, List.map_cons, List.prod_cons]

theorem prod_flatMap_replicate {ι α M : Type} [CommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).prod = ∏ i ∈ s, g (x i) ^ n i := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).prod =
      (l.map fun i => g (x i) ^ n i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_replicate, List.prod_replicate]
  rw [key, Finset.prod_map_toList]

theorem sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).sum =
      (l.map fun i => n i • g (x i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih, List.map_replicate, List.sum_replicate]
  rw [key, Finset.sum_map_toList]

end GlobalTheory.WeilDeligne.VirtualTrace


open GlobalTheory.WeilDeligne.VirtualTrace in
theorem GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ),
    (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) →
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ),
    (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) →
    ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  intro E Ω _ _ _ _ _ A w h f hf1 hf2 ι _ d a c hc
  classical
  let x : ι → Σ n : ℕ, WDRep h (Fin n → ℂ) := fun i => ⟨d i, a i⟩
  let L : (ι → ℕ) → List (Σ n : ℕ, WDRep h (Fin n → ℂ)) := fun n =>
    (Finset.univ : Finset ι).toList.flatMap fun i => List.replicate (n i) (x i)
  have hfL : ∀ n, f (WD.mk (listSum h (L n)).2) = ∏ i, f (WD.mk (a i)) ^ n i := fun n => by
    rw [map_listSum f hf1]
    exact prod_flatMap_replicate _ n x (fun y => f (WD.mk y.2))
  have htL : ∀ n σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L n)).2.ρ σ ^ k) =
      ∑ i, (n i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ ^ k) := fun n σ k => by
    rw [trace_listSum]
    rw [sum_flatMap_replicate _ n x (fun y => LinearMap.trace ℂ _ (y.2.ρ σ ^ k))]
    simp only [nsmul_eq_mul, x]
  have hcc : ∀ i, ((c i : ℤ) : ℂ) = (((c i).toNat : ℕ) : ℂ) - (((-c i).toNat : ℕ) : ℂ) := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    push_cast; ring
  have htr : ∀ σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L fun i => (c i).toNat)).2.ρ σ ^ k) =
      LinearMap.trace ℂ _ ((listSum h (L fun i => (-c i).toNat)).2.ρ σ ^ k) := fun σ k => by
    rw [htL, htL, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have := hc (σ ^ k)
    simp only [map_pow, hcc] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPQ : f (WD.mk (listSum h (L fun i => (c i).toNat)).2) =
      f (WD.mk (listSum h (L fun i => (-c i).toNat)).2) :=
    hf2 _ _ fun σ => by
      rw [WD.charPol_mk, WD.charPol_mk]
      exact GlobalTheory.T.charpoly_eq_of_trace_powers _ _ _ _ (htr σ)
  rw [hfL, hfL] at hPQ
  have hz : ∀ i, f (WD.mk (a i)) ^ c i =
      f (WD.mk (a i)) ^ (c i).toNat * (f (WD.mk (a i)) ^ (-c i).toNat)⁻¹ := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hPQ, mul_inv_cancel]
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.cyclotomicCharacterPadic_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  first | exact @GlobalTheory.Cyc.cyc_basic | exact GlobalTheory.Cyc.cyc_basic | (intros; apply GlobalTheory.Cyc.cyc_basic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.continuous_orbit_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨GlobalTheory.T.isLocallyConstant_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf), GlobalTheory.T.hasCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf)⟩,
    fun f hf => ⟨GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf), GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, GlobalTheory.T.partialFourierGLBlock_unitIndicator F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic F E htr)⟩

end GlobalTheory
end

section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  first | exact @GlobalTheory.PMonE.generalLemma_allOrders | exact GlobalTheory.PMonE.generalLemma_allOrders | (intros; apply GlobalTheory.PMonE.generalLemma_allOrders <;> assumption)
end

section

open GlobalTheory.UnitLemma

namespace GlobalTheory.UnitLemma

theorem UQ.finite_units_mod_sq : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [FiniteDimensional K.E L],
    Finite (Lˣ ⧸ (powMonoidHom 2 : Lˣ →* Lˣ).range) := by
  intro K L _ _ _
  letI := GlobalTheory.LocFieldOfDVR.valued K.O K.E
  letI : ValuativeRel K.E := .ofValuation (GlobalTheory.LocFieldOfDVR.val K.O K.E)
  haveI : (GlobalTheory.LocFieldOfDVR.val K.O K.E).Compatible := .ofValuation _
  haveI : IsNonarchimedeanLocalField K.E := by
    have : IsValuativeTopology K.E :=
      IsValuativeTopology.of_mem_nhds_iff_vle (GlobalTheory.LocFieldOfDVR.val K.O K.E)
        (fun {s x} => Valued.mem_nhds)
    have : ValuativeRel.IsNontrivial K.E :=
      (ValuativeRel.isNontrivial_iff_isNontrivial (GlobalTheory.LocFieldOfDVR.val K.O K.E)).mpr inferInstance
    have : LocallyCompactSpace K.E := GlobalTheory.LocFieldOfDVR.locallyCompactSpace
    exact {}
  obtain ⟨vrL, topL, hlocL, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension K.E L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K.E L).injective
  exact GroundTheory.LocalField.finite_quotient_range_pow_of_charZero (K := L) two_ne_zero

end GlobalTheory.UnitLemma
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.card_stable_lattices_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂), resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly ≠ 0 → ∀ (M₁ : Submodule O A₁) (M₂ : Submodule O A₂), IsLat O E M₁ → IsLat O E M₂ → (∀ y ∈ M₁, g₁ * y ∈ M₁) → (∀ y ∈ M₂, g₂ * y ∈ M₂) → (Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁, g₂) * y ∈ M) ∧ M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂} : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly) := by
  first | exact @GlobalTheory.StableLatCount.card_stable_lattices | exact GlobalTheory.StableLatCount.card_stable_lattices | (intros; apply GlobalTheory.StableLatCount.card_stable_lattices <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | exact GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | (intros; apply GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_unramified_odd_degree_quadratic_local_ext : ∀ (K : UQ) (d : ℕ), Odd d → ∃ (K' : UQ) (φ : K.E →+* K'.E), K'.q = K.q ^ d ∧ (∀ x, φ (K.c x) = K'.c (φ x)) ∧ (∀ x, val K'.O (φ x) = val K.O x) ∧ (K.Odd → K'.Odd) ∧ @Module.finrank K.E K'.E _ _ (φ.toAlgebra).toModule = d ∧ ∃ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) ∧ @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ := by
  first | exact @GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | exact GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext | (intros; apply GlobalTheory.UnitLemma.UnrExt.exists_unramified_ext <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_split_etaleHermitianPair_isometry : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  first | exact @GlobalTheory.JR.exists_split_et | exact GlobalTheory.JR.exists_split_et | (intros; apply GlobalTheory.JR.exists_split_et <;> assumption)
end
