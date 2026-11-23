module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle135
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GaloisCoh

theorem selmer_sha_eq_comap_ker :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), (∀ L : LocCond ρ (locFam S Av), Sel ρ (locFam S Av) (continuous_locFam S Av) L = (Submodule.pi Set.univ L).comap (loc1 S Av ρ)) ∧ Sha1 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc1 S Av ρ) ∧ Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ
  refine ⟨fun L => ?_, ?_, ?_⟩
  · ext x
    simp [mem_Sel, loc1, Submodule.mem_pi]
  · ext x
    simp [Sha1, loc1, Submodule.mem_iInf, LinearMap.mem_ker, funext_iff]
  · ext x
    simp [Sha2, loc2, Submodule.mem_iInf, LinearMap.mem_ker, funext_iff]

end GlobalTheory.CompanionTheory.GaloisCoh

end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem single_mul_mem_span_tdeg_pos {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d))
    (m : (cone S : AddSubmonoid (Gam n d))) (a : K) (x : R0 K n d S)
    (hx : x ∈ Submodule.span K {y : R0 K n d S | ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))),
      1 ≤ tdeg g ∧ y = mon K g hg}) :
    (AddMonoidAlgebra.single m a : R0 K n d S) * x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, h1, rfl⟩ := hy
    have e : (AddMonoidAlgebra.single m a : R0 K n d S) * mon K g hg =
        a • mon K (m.1 + g) ((cone S : AddSubmonoid (Gam n d)).add_mem m.2 hg) := by
      simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.smul_single, smul_eq_mul]
      rfl
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, ?_, rfl⟩)
    have h0 : 0 ≤ tdeg m.1 := m.2.2.2
    rw [tdeg_add]
    linarith
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exceptional_ideal_le_span_pos_degree : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (x : R0 K n d S),
    x ∈ I0 n K S → x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  intro K _ n d S x hx
  unfold I0 Ideal.span at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, _, rfl⟩ := hy
    exact Submodule.subset_span ⟨_, _, by rw [tdeg_oneE_inr], rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul]
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add f g hf hg => rw [add_mul]; exact Submodule.add_mem _ hf hg
    | single m a => exact single_mul_mem_span_tdeg_pos S m a x hx

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {n d : ℕ}

theorem cone_empty_nonneg {g : Gam n d} (hg : g ∈ (cone ∅ : AddSubmonoid (Gam n d))) (e : E n d) : 0 ≤ g e := by
  have hg' : (∀ l : Fin n, 0 ≤ g (Sum.inl l)) ∧ (∀ j ∉ (∅ : Finset (Fin d)), 0 ≤ g (Sum.inr j)) ∧
      0 ≤ tdeg g := hg
  rcases e with l | j
  · exact hg'.1 l
  · exact hg'.2.1 j (Finset.notMem_empty j)

theorem coe_mem_cone (f : E n d →₀ ℕ) :
    (fun e => (f e : ℤ) : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  show (∀ l : Fin n, (0 : ℤ) ≤ (f (Sum.inl l) : ℤ)) ∧
    (∀ j ∉ (∅ : Finset (Fin d)), (0 : ℤ) ≤ (f (Sum.inr j) : ℤ)) ∧ 0 ≤ tdeg (fun e => (f e : ℤ) : Gam n d)
  refine ⟨fun l => Int.natCast_nonneg _, fun j _ => Int.natCast_nonneg _, ?_⟩
  exact Finset.sum_nonneg fun j _ => Int.natCast_nonneg _

def expEquiv : (E n d →₀ ℕ) ≃+ (cone ∅ : AddSubmonoid (Gam n d)) where
  toFun f := ⟨fun e => (f e : ℤ), coe_mem_cone f⟩
  invFun g := Finsupp.equivFunOnFinite.symm fun e => (g.1 e).toNat
  left_inv f := by
    ext e
    simp
  right_inv g := by
    refine Subtype.ext (funext fun e => ?_)
    simpa using cone_empty_nonneg g.2 e
  map_add' f f' := by
    refine Subtype.ext (funext fun e => ?_)
    simp

def polyEquiv (K : Type) [Field K] : Bp K n d ≃ₐ[K] R0 K n d (∅ : Finset (Fin d)) :=
  AddMonoidAlgebra.domCongr K K expEquiv

theorem expEquiv_single (e : E n d) :
    (expEquiv (Finsupp.single e 1) : (cone ∅ : AddSubmonoid (Gam n d))) = ⟨oneE e, oneE_mem ∅ e⟩ := by
  refine Subtype.ext (funext fun e' => ?_)
  change ((Finsupp.single e 1 : E n d →₀ ℕ) e' : ℤ) = (Pi.single e (1 : ℤ) : E n d → ℤ) e'
  by_cases h : e' = e
  · subst h
    simp
  · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]

theorem poly_eq_polyEquiv (K : Type) [Field K] :
    poly n K (∅ : Finset (Fin d)) = (polyEquiv K).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro e
  rw [poly_X, polyEquiv,
    MvPolynomial.X, ← MvPolynomial.single_eq_monomial]
  erw [AddMonoidAlgebra.domCongr_single, expEquiv_single]
  rfl

theorem poly_bijective {K : Type} [Field K] {n d : ℕ} :
    Function.Bijective (poly n K (∅ : Finset (Fin d))) := by
  rw [poly_eq_polyEquiv]
  exact (polyEquiv K).bijective

end GlobalTheory.CompanionTheory.SurjectionOntoH4.PolyBij
end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

variable {K : Type} [Field K] {n d : ℕ}


variable (K n d) in
def tau : Bp K n d := ∏ e, MvPolynomial.X e

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (h : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst h; rfl

theorem mon_zero (M : AddSubmonoid (Gam n d)) : mon K (0 : Gam n d) M.zero_mem = 1 := rfl

theorem mon_pow {M : AddSubmonoid (Gam n d)} (g : Gam n d) (hg : g ∈ M) (k : ℕ) :
    mon K g hg ^ k = mon K (k • g) (M.nsmul_mem hg k) := by
  induction k with
  | zero => rw [pow_zero]; exact ((mon_congr (zero_nsmul g) _ M.zero_mem).trans (mon_zero M)).symm
  | succ k ih => rw [pow_succ, ih, mon_mul]; exact mon_congr (succ_nsmul g k).symm _ _

theorem mon_prod {M : AddSubmonoid (Gam n d)} (s : Finset (E n d)) (f : E n d → Gam n d) (hf : ∀ e, f e ∈ M) :
    ∏ e ∈ s, mon K (f e) (hf e) = mon K (∑ e ∈ s, f e) (M.sum_mem fun e _ => hf e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact (mon_zero M).symm
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha).symm _ _

theorem poly_monomial (S : Finset (Fin d)) (k : E n d → ℕ) :
    poly n K S (∏ e, MvPolynomial.X e ^ k e) =
      mon K (∑ e, k e • oneE e) ((cone S).sum_mem fun e _ => (cone S).nsmul_mem (oneE_mem S e) (k e)) := by
  rw [map_prod]
  simp only [map_pow, poly_X, mon_pow]
  exact mon_prod _ _ _

theorem poly_tau_pow (S : Finset (Fin d)) (N : ℕ) :
    ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), (∀ e, g e = N) ∧
      poly n K S (tau K n d ^ N) = mon K g hg := by
  refine ⟨N • ∑ e, oneE e, (cone S).nsmul_mem ((cone S).sum_mem fun e _ => oneE_mem S e) N, fun e => ?_, ?_⟩
  · simp only [Pi.smul_apply, Finset.sum_apply, oneE, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul, mul_one]
  · rw [map_pow, tau, map_prod]
    simp only [poly_X]
    rw [mon_prod, mon_pow]

theorem exists_poly (S : Finset (Fin d)) (y : R0 K n d S) :
    ∃ (N : ℕ) (b : Bp K n d), poly n K S (tau K n d ^ N) * y = poly n K S b := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨N₁, b₁, h₁⟩ := hf
    obtain ⟨N₂, b₂, h₂⟩ := hg
    refine ⟨N₁ + N₂, tau K n d ^ N₂ * b₁ + tau K n d ^ N₁ * b₂, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m c =>
    obtain ⟨g, hg⟩ := m
    let N : ℕ := ∑ e, (g e).natAbs
    have hN : ∀ e, 0 ≤ (N : ℤ) + g e := fun e => by
      have h1 : (g e).natAbs ≤ N := Finset.single_le_sum (f := fun e => (g e).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
      omega
    obtain ⟨g', hg', hc, hp⟩ := poly_tau_pow (K := K) (n := n) S N
    refine ⟨N, c • ∏ e, MvPolynomial.X e ^ ((N : ℤ) + g e).toNat, ?_⟩
    have h1 : (AddMonoidAlgebra.single ⟨g, hg⟩ c : R0 K n d S) = c • mon K g hg := by
      simp [mon]
    rw [map_smul, poly_monomial, h1, hp, mul_smul_comm, mon_mul]
    congr 1
    refine mon_congr ?_ _ _
    funext e
    have h2 : (∑ e', ((N : ℤ) + g e').toNat • (oneE e' : Gam n d)) e = ((N : ℤ) + g e).toNat := by
      simp [oneE, Finset.sum_apply, Pi.single_apply]
    rw [h2, Pi.add_apply, hc, Int.toNat_of_nonneg (hN e)]

theorem mul_injective (T : Finset (Fin d)) (N : ℕ) :
    Function.Injective fun x : R0 K n d T => poly n K T (tau K n d ^ N) * x := by
  intro x y hxy
  have hi : Function.Injective (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) :=
    AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective _)
  apply hi
  obtain ⟨g, hg, -, hp⟩ := poly_tau_pow (K := K) (n := n) T N
  have h := congrArg (incl (K := K) (le_top : (cone T : AddSubmonoid (Gam n d)) ≤ ⊤)) hxy
  simp only [map_mul, hp, incl_mon] at h
  have hu : IsUnit (mon K g (AddSubmonoid.mem_top g) : Lr K n d) := by
    refine isUnit_iff_exists_inv.2 ⟨mon K (-g) (AddSubmonoid.mem_top _), ?_⟩
    rw [mon_mul]
    exact (mon_congr (add_neg_cancel g) _ _).trans (mon_zero _)
  exact hu.mul_left_cancel h

variable {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d)

theorem eq_zero_of_mul {T : Finset (Fin d)} (θ' : R0 K n d T →ₐ[K] C.R T)
    (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)) (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ'))
    (N : ℕ) (z : C.R T) (hz : toR C T (phi C (tau K n d ^ N)) * z = 0) : z = 0 := by
  haveI := etale_Aa C
  haveI : Module.Flat (Bp K n d) (Aa C) := Algebra.Smooth.flat _ _
  let f : R0 K n d T →ₗ[Bp K n d] R0 K n d T := LinearMap.mulLeft (Bp K n d) (poly n K T (tau K n d ^ N))
  have hf : Function.Injective f := mul_injective T N
  have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := Aa C) f hf
  let v : Rb C T := toR C T (phi C (tau K n d ^ N))
  have key : ∀ w : TensorProduct (Bp K n d) (Aa C) (R0 K n d T),
      hb.equiv (f.lTensor (Aa C) w) = v * hb.equiv w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' => simp only [map_add (f := _), hu, hu', mul_add]
    | tmul a x =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      change toR C T a * θ' (poly n K T (tau K n d ^ N) * x) = toR C T (phi C (tau K n d ^ N)) * (toR C T a * θ' x)
      rw [map_mul, hθ']
      ring
  have main : ∀ z' : Rb C T, v * z' = 0 → z' = 0 := by
    intro z' hz'
    have hw : f.lTensor (Aa C) (hb.equiv.symm z') = 0 := by
      apply hb.equiv.injective
      rw [map_zero, key, LinearEquiv.apply_symm_apply]
      exact hz'
    have h3 := hl (hw.trans (map_zero _).symm)
    exact hb.equiv.symm.map_eq_zero_iff.1 h3
  exact main z hz

theorem theta_unique {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T)
    (h₁ : ∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) (h₂ : ∀ b, θ₂ (poly n K S b) = toR C T (phi C b))
    (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b))
    (hb : IsBaseChange (Aa C) (thetaLin C θ' hθ')) : θ₁ = θ₂ := by
  refine AlgHom.ext fun y => ?_
  obtain ⟨N, b, h⟩ := exists_poly S y
  have e₁ := congrArg θ₁ h
  have e₂ := congrArg θ₂ h
  rw [map_mul, h₁, h₁] at e₁
  rw [map_mul, h₂, h₂] at e₂
  refine sub_eq_zero.1 (eq_zero_of_mul C θ' hθ' hb N _ ?_)
  rw [mul_sub, e₁, e₂, sub_self]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique
end
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Away

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_pow {M : AddSubmonoid (Gam n d)} (c : Gam n d) (hc : c ∈ M) (N : ℕ) :
    mon K c hc ^ N = mon K (N • c) (M.nsmul_mem hc N) := by
  simp only [mon, AddMonoidAlgebra.single_pow, one_pow]
  rfl

theorem incl_injective {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') :
    Function.Injective (incl (K := K) h) := by
  intro x y hxy
  simp only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy

theorem exists_mul_pow_eq_incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M)
    (hg : ∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) (z : Rg K M') :
    ∃ (N : ℕ) (a : Rg K M), z * incl h (mon K c hc ^ N) = incl h a := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg' =>
    obtain ⟨N₁, a₁, h₁⟩ := hf
    obtain ⟨N₂, a₂, h₂⟩ := hg'
    refine ⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩
    rw [map_add (f := _), map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m k =>
    obtain ⟨N, hN⟩ := hg m.1 m.2
    refine ⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩
    rw [mon_pow, incl_mon]
    simp only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]
    simp
    rfl

theorem isLocalization_away : ∀ {K : Type} [Field K] {n d : ℕ} {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M), -c ∈ M' → (∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) → letI := (incl (K := K) h).toRingHom.toAlgebra; IsLocalization.Away (mon K c hc) (Rg K M') := by
  intro K _ n d M M' h c hc hneg hg
  letI := (incl (K := K) h).toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x := fun _ => rfl
  have hu : IsUnit (incl h (mon K c hc)) := by
    rw [incl_mon]
    refine IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_
    rw [mon_mul]
    simp only [mon, add_neg_cancel]
    rfl
  refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · rintro ⟨_, N, rfl⟩
    rw [hal, map_pow]
    exact hu.pow N
  · obtain ⟨N, a, ha⟩ := exists_mul_pow_eq_incl h c hc hg z
    exact ⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩
  · rw [incl_injective h hxy]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Away
end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem sub_oneE_mem_cone {n d : ℕ} {S : Finset (Fin d)} {g : Gam n d}
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) (ht : 1 ≤ tdeg g) (k : Fin d)
    (hk : k ∈ S ∨ 1 ≤ g (Sum.inr k)) :
    g - oneE (Sum.inr k) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have hg' : (∀ l, 0 ≤ g (Sum.inl l)) ∧ (∀ j, j ∉ S → 0 ≤ g (Sum.inr j)) ∧ 0 ≤ tdeg g := hg
  obtain ⟨h1, h2, _⟩ := hg'
  show (∀ l, 0 ≤ (g - oneE (Sum.inr k) : Gam n d) (Sum.inl l)) ∧
    (∀ j, j ∉ S → 0 ≤ (g - oneE (Sum.inr k) : Gam n d) (Sum.inr j)) ∧ 0 ≤ tdeg (g - oneE (Sum.inr k))
  refine ⟨fun l => ?_, fun j hj => ?_, ?_⟩
  · simp only [oneE, Pi.sub_apply]
    rw [Pi.single_eq_of_ne Sum.inl_ne_inr, sub_zero]
    exact h1 l
  · by_cases hjk : j = k
    · subst hjk
      have h1' : 1 ≤ g (Sum.inr j) := hk.resolve_left hj
      simp only [oneE, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp only [oneE, Pi.sub_apply]
      rw [Pi.single_eq_of_ne (fun h => hjk (Sum.inr_injective h)), sub_zero]
      exact h2 j hj
  · have hs : ∑ j, (oneE (Sum.inr k) : Gam n d) (Sum.inr j) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [oneE]
      · intro b _ hb
        simp only [oneE]
        exact Pi.single_eq_of_ne (fun h => hb (Sum.inr_injective h)) _
      · intro h
        exact absurd (Finset.mem_univ k) h
    show 0 ≤ ∑ j, (g - oneE (Sum.inr k) : Gam n d) (Sum.inr j)
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hs]
    have ht' : 1 ≤ ∑ j, g (Sum.inr j) := ht
    omega

theorem monomial_mem_exceptional_ideal {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) (ht : 1 ≤ tdeg g) : mon K g hg ∈ I0 n K S := by
  have hex : ∃ k, (S = ∅ ∨ k ∈ S) ∧ (k ∈ S ∨ 1 ≤ g (Sum.inr k)) := by
    by_cases hS : S = ∅
    · by_contra hno
      push_neg at hno
      have hsum : ∑ j, g (Sum.inr j) ≤ 0 := Finset.sum_nonpos fun j _ => by
        have := (hno j (Or.inl hS)).2
        omega
      have ht' : 1 ≤ ∑ j, g (Sum.inr j) := ht
      omega
    · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hS
      exact ⟨k, Or.inr hk, Or.inl hk⟩
  obtain ⟨k, hkS, hk⟩ := hex
  have h' := sub_oneE_mem_cone hg ht k hk
  have hmul : mon K g hg =
      mon K (oneE (Sum.inr k)) (oneE_mem S _) * mon K (g - oneE (Sum.inr k)) h' := by
    simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one]
    congr 1
    ext1
    simp
  rw [hmul]
  unfold I0
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k, hkS, rfl⟩)

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

section

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch


theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

theorem _root_.GlobalTheory.T.cochain_cohomology_nerve_homology_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    Nonempty (LinearMap.ker (MainStatements.Hodge.dn F 0) ≃ₗ[R] (nerveCx.obj (toMod F)).homology 0) ∧
      ∀ n, Nonempty (MainStatements.Hodge.Hs F n ≃ₗ[R] (nerveCx.obj (toMod F)).homology (n + 1)) :=
  @GlobalTheory.CompanionTheory.Hodge.Nerve.Low.homology_nerveCx
end
