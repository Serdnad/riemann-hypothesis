module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle005
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.CoefMap

theorem restrict_pull1_injective_of_sep_glue {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (hsep : ∀ (T : C) (x : F.obj T), (∀ t (u : T ⟶ G.obj t), mp F u x = 0) → x = 0)
    (hglue : ∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)),
      (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) →
      ∃ x : F.obj T, ∀ t u, mp F u x = s t u) :
    Function.Injective (CoefMap.restrict F G).pull1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
  obtain ⟨g₀, hg⟩ := hc
  let g : ∀ t, F.obj (G.obj t) := fun t ↦ g₀ t
  have hg' : ∀ t t' (a : t ⟶ t'), g t' - mp F (G.map a) (g t) = f.1 _ _ (G.map a) := fun t t' a ↦
    congrFun (congrFun (congrFun hg t) t') a
  have h1 : ∀ T : C, ∃ x : F.obj T, ∀ t (u : T ⟶ G.obj t), mp F u x = g t - f.1 T _ u := by
    intro T
    refine hglue T (fun t u ↦ g t - f.1 T _ u) fun t t' u a ↦ ?_
    have k1 := Z1.comp f u (G.map a)
    have k2 := hg' t t' a
    simp only [map_sub]
    linear_combination k2 - k1
  choose x hx using h1
  refine H1.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' φ
  rw [amitsur_d0_apply]
  refine (sub_eq_zero.1 (hsep T' _ fun t u ↦ ?_)).symm
  have k1 := Z1.comp f φ u
  have k2 := hx T' t u
  have k3 := hx T t (φ ≫ u)
  rw [mp_comp] at k3
  simp only [map_sub]
  linear_combination k3 - k2 - k1

end GlobalTheory.CatCoh.CoefMap
end
end

section

open IsDedekindDomain

noncomputable section

namespace GlobalTheory.AdeleSplitP

open GlobalTheory.LKTrip Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

def placeP (p : ℕ) [hp : Fact p.Prime] : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).2
    (Nat.prime_iff_prime_int.mp hp.out)
  ne_bot := by simpa using hp.out.ne_zero

theorem primesEquiv_placeP (p : ℕ) [hp : Fact p.Prime] :
    primesEquiv (placeP p) = (⟨p, hp.out⟩ : Nat.Primes) := by
  apply Subtype.ext
  change natGenerator (placeP p) = p
  have h1 := span_natGenerator (placeP p)
  have he : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ :=
    RingEquiv.ext fun x ↦ by simpa using eq_intCast (Rat.IsIntegralClosure.intEquiv ℤ) x
  have h2 : (placeP p).asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) = (placeP p).asIdeal := by
    rw [he]
    exact Ideal.map_id _
  rw [h2] at h1
  change Ideal.span {((natGenerator (placeP p) : ℕ) : ℤ)} = Ideal.span {(p : ℤ)} at h1
  rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h1
  simpa using h1

def compP (p : ℕ) [hp : Fact p.Prime] : FiniteAdeleRing ℤ ℚ →+* ℚ_[p] :=
  ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).toRingEquiv.toRingHom.comp
    (adicCompletion.padicEquiv (placeP p)).toRingEquiv.toRingHom).comp
    (RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum ℤ ↦ v.adicCompletion ℚ) (placeP p))

theorem compP_apply (p : ℕ) [Fact p.Prime] (a : FiniteAdeleRing ℤ ℚ) :
    compP p a = ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
      (adicCompletion.padicEquiv (placeP p) (a (placeP p))) := rfl

theorem continuous_compP (p : ℕ) [Fact p.Prime] : Continuous (compP p) :=
  show Continuous (fun a ↦ compP p a) from (ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).continuous.comp
    ((adicCompletion.padicEquiv (placeP p)).continuous.comp (RestrictedProduct.continuous_eval _))

theorem restr_eval (p : ℕ) (a : FiniteAdeleRing ℤ ℚ) (w : AwayP p) :
    AfP.eval w (AfP.restr p a) = a w.1 := rfl

theorem finiteAdeleRingAway_ext {p : ℕ} {b c : AfP p} (h : ∀ w, AfP.eval w b = AfP.eval w c) : b = c :=
  Subtype.ext (funext fun w ↦ h w)

theorem eq_placeP {p : ℕ} [Fact p.Prime] {v : HeightOneSpectrum ℤ}
    (hv : v.asIdeal = Ideal.span {(p : ℤ)}) : v = placeP p :=
  HeightOneSpectrum.ext hv

theorem finiteAdele_split (p : ℕ) [Fact p.Prime] :
    ∃ π : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] ℚ_[p], Continuous π ∧
      Function.Bijective (fun a ↦ (GlobalTheory.LKTrip.AfP.restr p a, π a)) := by
  refine ⟨(compP p).toRatAlgHom, continuous_compP p, ?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    refine FiniteAdeleRing.ext _ fun v ↦ ?_
    by_cases hv : v.asIdeal = Ideal.span {(p : ℤ)}
    · obtain rfl := eq_placeP hv
      have h2' : compP p a = compP p b := h2
      rw [compP_apply, compP_apply] at h2'
      exact (adicCompletion.padicEquiv (placeP p)).injective
        ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).injective h2')
    · exact congrArg (AfP.eval ⟨v, hv⟩) h1
  · rintro ⟨b, y⟩
    classical
    let x0 : (placeP p).adicCompletion ℚ := (adicCompletion.padicEquiv (placeP p)).symm
      ((ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)).symm y)
    let g0 : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := fun v ↦
      if h : v.asIdeal = Ideal.span {(p : ℤ)} then 0 else AfP.eval ⟨v, h⟩ b
    let g : ∀ v : HeightOneSpectrum ℤ, v.adicCompletion ℚ := Function.update g0 (placeP p) x0
    have hg : ∀ v (hv : v.asIdeal ≠ Ideal.span {(p : ℤ)}), g v = AfP.eval ⟨v, hv⟩ b := by
      intro v hv
      have hv0 : v ≠ placeP p := fun h ↦ hv (h ▸ rfl)
      simp only [g, g0, Function.update_of_ne hv0, dif_neg hv]
    have hS : {w : AwayP p | ¬ AfP.eval w b ∈ w.1.adicCompletionIntegers ℚ}.Finite :=
      Filter.eventually_cofinite.1 b.2
    have hfin : {v : HeightOneSpectrum ℤ | ¬ g v ∈ v.adicCompletionIntegers ℚ}.Finite := by
      refine ((hS.image Subtype.val).insert (placeP p)).subset fun v hv ↦ ?_
      by_cases hv0 : v = placeP p
      · exact Or.inl hv0
      · have hv' : v.asIdeal ≠ Ideal.span {(p : ℤ)} := fun h ↦ hv0 (eq_placeP h)
        refine Or.inr ⟨⟨v, hv'⟩, ?_, rfl⟩
        have hv2 : ¬ g v ∈ v.adicCompletionIntegers ℚ := hv
        rw [hg v hv'] at hv2
        exact hv2
    let A : FiniteAdeleRing ℤ ℚ := ⟨g, Filter.eventually_cofinite.2 hfin⟩
    refine ⟨A, Prod.ext ?_ ?_⟩
    · show AfP.restr p A = b
      refine finiteAdeleRingAway_ext fun w ↦ ?_
      rw [restr_eval]
      exact hg w.1 w.2
    · show compP p A = y
      change ContinuousAlgEquiv.cast (R := ℚ) (A := fun q : Nat.Primes ↦ ℚ_[q]) (primesEquiv_placeP p)
        (adicCompletion.padicEquiv (placeP p) (g (placeP p))) = y
      simp only [g, Function.update_self, x0, ContinuousAlgEquiv.apply_symm_apply]

end GlobalTheory.AdeleSplitP
end
end

section

namespace GlobalTheory.LatticeIntegralCoordinates

theorem exists_basis_of_lattice (O E V : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [AddCommGroup V] [Module E V] [Module O V]
    [IsScalarTower O E V] (L : Submodule O V) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank E V)) E V,
      ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap O E).range := by
  classical
  haveI : Module.IsTorsionFree O V := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro c v h
    rw [← algebraMap_smul E c v] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective O E) (by simpa using h)
    · right; exact h
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O L := inferInstance
  let bL := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (bL i : V)
  have hli : LinearIndependent O v :=
    bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent E v := hli.localization E (nonZeroDivisors O)
  have hL : Submodule.span O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range bL := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, bL.span_eq, Submodule.map_top, Submodule.range_subtype]
  have htop : ⊤ ≤ Submodule.span E (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    exact Submodule.span_subset_span O E _ (hL.ge hx)
  let b0 := Module.Basis.mk hliE htop
  have hb0 : ∀ j, b0 j = v j := fun j => Module.Basis.mk_apply hliE htop j
  have hcard := Module.finrank_eq_card_basis b0
  let e := Fintype.equivFinOfCardEq hcard.symm
  refine ⟨b0.reindex e, fun y => ⟨fun hy i => ?_, fun hy => ?_⟩⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hL.ge hy)
    have h1 : ∑ j, c j • v j = ∑ j, algebraMap O E (c j) • b0 j :=
      Finset.sum_congr rfl fun j _ => by rw [hb0, algebraMap_smul]
    rw [Module.Basis.repr_reindex_apply, h1, b0.repr_sum_self]
    exact ⟨_, rfl⟩
  · rw [← b0.sum_repr y]
    refine L.sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := hy (e j)
    rw [Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply] at hc
    rw [← hc, algebraMap_smul, hb0]
    exact L.smul_mem c (bL j).2

theorem lattice_eq_integral_coords :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
      [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (L : Submodule K.O V),
      L.FG → Submodule.span K.E (L : Set V) = ⊤ →
      ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V,
        ∀ y : V, y ∈ L ↔ ∀ i, b.repr y i ∈ (algebraMap K.O K.E).range :=
  fun K V _ _ _ _ _ L hfg hspan => exists_basis_of_lattice K.O K.E V L hfg hspan

end GlobalTheory.LatticeIntegralCoordinates
end

section

namespace GlobalTheory.ScalarSigmaBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem sig_smul (r : K.E) (x : B.A) : B.σ (r • x) = K.c r • B.σ x := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

theorem sig_sum {ι : Type} (s : Finset ι) (f : ι → K.E) (v : ι → B.A) :
    B.σ (∑ i ∈ s, f i • v i) = ∑ i ∈ s, K.c (f i) • B.σ (v i) := by

  rw [map_sum]; simp only [sig_smul]

noncomputable def sigBasis {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) : Module.Basis (Fin n) K.E B.A :=
  Module.Basis.mk (v := fun i => B.σ (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro f hf i
      have h1 : B.σ (∑ k, f k • B.σ (b k)) = 0 := by rw [hf, map_zero]
      rw [sig_sum] at h1
      simp only [B.σ_σ] at h1
      have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
      have : K.c (f i) = K.c 0 := by rw [h2, map_zero]
      exact K.c.injective this)
    (by
      intro x _
      have h := sig_sum B Finset.univ (fun k => b.repr (B.σ x) k) (fun k => b k)
      have hx : x = ∑ k, K.c (b.repr (B.σ x) k) • B.σ (b k) := by
        rw [← h, b.sum_repr, B.σ_σ]
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem sigBasis_apply {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (i : Fin n) :
    sigBasis B b i = B.σ (b i) := by
  simp [sigBasis]

theorem sigBasis_repr {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (z : B.A) (k : Fin n) :
    (sigBasis B b).repr (B.σ z) k = K.c (b.repr z k) := by
  have hz : B.σ z = ∑ i, K.c (b.repr z i) • sigBasis B b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [sig_sum]
    simp only [sigBasis_apply]
  rw [hz, Module.Basis.repr_sum_self]

theorem trace_sig (y : B.A) : Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  let b := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace (sigBasis B b), Algebra.trace_eq_matrix_trace b]

  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigBasis_apply, ← map_mul, sigBasis_repr]

theorem core (a : ℕ) (β : B.A) (hβ : B.σ β = β * ((-1 : B.A) ^ (a - 1) * B.g))
    (b : Module.Basis (Fin a) K.E B.A) (i j : Fin a) :
    K.c (B.herm β (b i) (b j)) = (-1 : K.E) ^ (a - 1) *
      ∑ k, B.herm β (b k) (b i) * LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) k j := by
  have hg : B.g * b j = ∑ k, b.repr (B.g * b j) k • b k := (b.sum_repr _).symm
  have e1 : B.σ (β * b i * B.σ (b j)) =
      algebraMap K.E B.A ((-1 : K.E) ^ (a - 1)) * (β * (B.g * b j) * B.σ (b i)) := by
    rw [map_mul, map_mul, B.σ_σ, hβ]
    simp only [map_pow, map_neg, map_one]
    ring
  have e2 : β * (B.g * b j) * B.σ (b i) = ∑ k, b.repr (B.g * b j) k • (β * b k * B.σ (b i)) := by
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]

  rw [InvAlg.herm, ← trace_sig, e1, e2, ← Algebra.smul_def, LinearMap.map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, mul_comm]
  rfl

theorem main : ∀ {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [inst : Field L] (e : GlobalTheory.UnitLemma.UQ.E K ≃+* L) (c : L →+* L), (∀ (x : GlobalTheory.UnitLemma.UQ.E K), (e : GlobalTheory.UnitLemma.UQ.E K → L) ((GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) x) = (c : L → L) ((e : GlobalTheory.UnitLemma.UQ.E K → L) x)) → ∀ (a : ℕ) (β : GlobalTheory.UnitLemma.InvAlg.A B), (GlobalTheory.UnitLemma.InvAlg.σ B : GlobalTheory.UnitLemma.InvAlg.A B → GlobalTheory.UnitLemma.InvAlg.A B) β = β * ((-1 : GlobalTheory.UnitLemma.InvAlg.A B) ^ (a - (1 : ℕ)) * GlobalTheory.UnitLemma.InvAlg.g B) → ∀ (b : Module.Basis (Fin a) (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.A B)), Matrix.map (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) (⇑c : L → L) = (-1 : L) ^ (a - (1 : ℕ)) • (Matrix.transpose (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) * Matrix.map ((LinearMap.toMatrix b b : (GlobalTheory.UnitLemma.InvAlg.A B →ₗ[GlobalTheory.UnitLemma.UQ.E K] GlobalTheory.UnitLemma.InvAlg.A B) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) (LinearMap.mulLeft (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.g B))) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) := by
  intro K B L _ e c hc a β hβ b
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  rw [← hc, core B a β hβ b i j]

  simp only [map_mul, map_sum, map_pow, map_neg, map_one]

end GlobalTheory.ScalarSigmaBasis
end

section

open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable section

namespace InertUnit

variable {K : UQ} {P : K.E[X]}

theorem coeff_mul (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    K.c (P.coeff 0) * P.coeff 0 = 1 := by
  have h := congrArg (fun Q => Q.coeff 0) hr
  simp only [coeff_C_mul, coeff_zero_reverse] at h
  rw [h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]

def rootInv (P : K.E[X]) : AdjoinRoot P :=
  -(algebraMap K.E (AdjoinRoot P) (K.c (P.coeff 0))) * aeval (AdjoinRoot.root P) P.divX

theorem root_mul_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot.root P * rootInv P = 1 := by
  have h0 : aeval (AdjoinRoot.root P) P = 0 := AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self
  have h1 := congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)
  rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at h1
  have h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0) :=
    eq_neg_of_add_eq_zero_left h1
  unfold rootInv
  rw [mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]

theorem eval_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    P.eval₂ ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) = 0 := by
  have hu := root_mul_rootInv hP hr
  letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩
  rw [← eval₂_map, ← eval₂_reverse_mul_pow]
  have : ⅟(rootInv P) = AdjoinRoot.root P := rfl
  rw [this, ← hr, eval₂_mul, eval₂_C]
  have h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0 := AdjoinRoot.eval₂_root P
  rw [h0, mul_zero, zero_mul]

def sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) (eval_rootInv hP hr)

theorem sig_alg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) (e : K.E) :
    sig hP hr (algebraMap K.E (AdjoinRoot P) e) = algebraMap K.E (AdjoinRoot P) (K.c e) := by
  rw [AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]
  rfl

theorem sig_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    sig hP hr (AdjoinRoot.root P) = rootInv P := AdjoinRoot.lift_root _

theorem sig_sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (sig hP hr).comp (sig hP hr) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]
  · simp only [RingHom.comp_apply, RingHom.id_apply, sig_root]
    have hu := root_mul_rootInv hP hr
    have h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1 := by rw [← map_mul, hu, map_one]
    rw [sig_root] at h1
    calc sig hP hr (rootInv P) = (AdjoinRoot.root P * rootInv P) * sig hP hr (rootInv P) := by rw [hu, one_mul]
      _ = AdjoinRoot.root P * (rootInv P * sig hP hr (rootInv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]

def invAlg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) : InvAlg K where
  A := AdjoinRoot P
  fd := (AdjoinRoot.powerBasis hP.ne_zero).finite
  σ := RingEquiv.ofRingHom (sig hP hr) (sig hP hr) (sig_sig hP hr) (sig_sig hP hr)
  σ_σ := fun y => congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) (sig_sig hP hr)
  σ_alg := sig_alg hP hr
  g := AdjoinRoot.root P

theorem charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

end InertUnit

open InertUnit in
theorem exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end
end GlobalTheory.UnitLemma
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_isIntegral (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A) :
    Algebra.IsIntegral R (firstAndFinite R A k F) := by
  unfold firstAndFinite
  apply Algebra.IsIntegral.adjoin
  rintro x (⟨a, rfl⟩ | hx)
  · exact (Algebra.IsIntegral.isIntegral a).map _
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨a, -, rfl⟩ := hi
    exact (Algebra.IsIntegral.isIntegral a).map _

end GlobalTheory.EtC
end
