module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle155
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GaloisCoh

theorem finite_of_finite_ker {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Finite B] (f : A →ₗ[R] B)
    (hk : Finite (LinearMap.ker f)) : Finite A := by
  classical
  let s : B → A := fun b => if h : ∃ a, f a = b then h.choose else 0
  have hs : ∀ a, f (s (f a)) = f a := fun a => by
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [s, dif_pos h]
    exact h.choose_spec
  let φ : A → B × LinearMap.ker f := fun a =>
    (f a, ⟨a - s (f a), by simp [LinearMap.mem_ker, hs]⟩)
  refine Finite.of_injective φ fun a b hab => ?_
  have h1 : f a = f b := congrArg Prod.fst hab
  have h2 : a - s (f a) = b - s (f b) := congrArg (fun x => (x.2 : A)) hab
  rw [h1] at h2
  exact sub_left_injective h2

theorem global_finite_of_poitouTate : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), μ.comp (toGS Ω _) = cycMod F Ω l r → Finite (TDual (ZMod (l ^ r)) M) → LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → ShaDual S Av μ ρ → Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Finite (H0 (twDual μ ρ)) ∧ Finite (H1 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hμ hT hF hr hA _ hSha
  have hρ' : ContAction (twDual μ ρ) := GlobalTheory.CompanionTheory.GalDual.contAction_twDual F Ω l r M S Av μ ρ hρ hμ
  obtain ⟨-, hS1, hS2⟩ := selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  obtain ⟨-, hT1, -⟩ := selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  have hloc := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hF hr hA
  have hlocT := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hF hr hA
  have p1 : Finite (∀ v : S, H1 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.1
    inferInstance
  have p2 : Finite (∀ v : S, H2 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.2
    inferInstance
  have pT : Finite (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) :=
    haveI := fun v => (hlocT v).2.1
    inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av ρ) ?_
    rw [← hS1]
    exact hSha.2.1
  · refine finite_of_finite_ker (loc2 S Av ρ) ?_
    rw [← hS2]
    exact hSha.1.2.1
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av (twDual μ ρ)) ?_
    rw [← hT1]
    exact hSha.1.1

end GlobalTheory.CompanionTheory.GaloisCoh

end
end

section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4


open TensorProduct in
theorem isBaseChange_of_presentation {B A P Q ι : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing Q]
    [Algebra B A] [Algebra B P] [Algebra A Q] [Algebra B Q] [IsScalarTower B A Q]
    (θ : P →ₐ[B] Q) (u : ι → Q) (v : ι → P) (k : ι) (b : ι → B)
    (hv : ∀ j, θ (v j) = u j)
    (hsurj : Function.Surjective (MvPolynomial.aeval (R := A) (S₁ := Q) u))
    (hker : RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j)))
    (hvk : v k = 1) (hb : ∀ j, algebraMap B P (b j) = algebraMap B P (b k) * v j)
    (hadj : Algebra.adjoin B (Set.range v) = ⊤) :
    IsBaseChange A θ.toLinearMap := by
  let f : MvPolynomial ι A →ₐ[A] Q := MvPolynomial.aeval u
  let g : MvPolynomial ι A →ₐ[A] A ⊗[B] P := MvPolynomial.aeval fun j => (1 : A) ⊗ₜ[B] v j
  have key : ∀ c : B, (algebraMap B A c) ⊗ₜ[B] (1 : P) = (1 : A) ⊗ₜ[B] algebraMap B P c := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker g.toRingHom := by
    change RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := Q) u).toRingHom ≤ _
    rw [hker]
    refine Ideal.span_le.2 ?_
    rintro _ (rfl | ⟨j, rfl⟩)
    · change g _ = 0
      simp [g, hvk, Algebra.TensorProduct.one_def]
    · change g _ = 0
      have e : g (MvPolynomial.C (algebraMap B A (b j)) - MvPolynomial.C (algebraMap B A (b k)) * MvPolynomial.X j) =
          (algebraMap B A (b j)) ⊗ₜ[B] (1 : P) - ((algebraMap B A (b k)) ⊗ₜ[B] (1 : P)) * ((1 : A) ⊗ₜ[B] v j) := by
        simp [g, Algebra.TensorProduct.algebraMap_apply]
      rw [e, key, key, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb, sub_self]
  have hmem : ∀ p ∈ RingHom.ker f, g p = 0 := fun p hp => hle hp
  let h : Q →ₐ[A] A ⊗[B] P :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g hmem).comp (Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.toAlgHom
  have hh : ∀ p, h (f p) = g p := by
    intro p
    have e : (Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g hmem ((Ideal.quotientKerAlgEquivOfSurjective (f := f) hsurj).symm (f p)) = _
    rw [e]
    rfl
  let L : A ⊗[B] P →ₐ[A] Q := Algebra.TensorProduct.lift (Algebra.ofId A Q) θ fun _ _ => Commute.all _ _
  have hL1 : ∀ y, L ((1 : A) ⊗ₜ[B] y) = θ y := by
    intro y
    simp [L]
  have hLg : L.comp g = f := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [g, f, hL1, hv]
  have hLh : L.comp h = AlgHom.id A Q := by
    refine AlgHom.ext fun r => ?_
    obtain ⟨p, rfl⟩ := hsurj r
    change L (h (f p)) = f p
    rw [hh]
    exact DFunLike.congr_fun hLg p
  have hhL : h.comp L = AlgHom.id A (A ⊗[B] P) := by
    apply Algebra.TensorProduct.ext
    · refine AlgHom.ext fun a => ?_
      have := (h.comp L).commutes a
      simpa [Algebra.TensorProduct.algebraMap_apply] using this
    · refine AlgHom.ext_of_adjoin_eq_top hadj ?_
      rintro _ ⟨j, rfl⟩
      change h (L ((1 : A) ⊗ₜ[B] v j)) = (1 : A) ⊗ₜ[B] v j
      have e : u j = f (MvPolynomial.X j) := by simp [f]
      rw [hL1, hv, e, hh]
      simp [g]
  let eq : A ⊗[B] P ≃ₐ[A] Q := AlgEquiv.ofAlgHom L h hLh hhL
  exact IsBaseChange.of_equiv eq.toLinearEquiv fun x => hL1 x

theorem mon_eq_one {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g : Gam n d} (hg : g ∈ M) (h : g = 0) :
    mon K g hg = 1 := by
  subst h
  rfl

theorem mon_congr {K : Type} [Field K] {n d : ℕ} {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (hg : g ∈ M) (hg' : g' ∈ M)
    (h : g = g') : mon K g hg = mon K g' hg' := by
  subst h
  rfl

theorem theta_one {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (k : Fin d) :
    ∃ (θ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b)),
      (∀ j, θ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) ∧
        IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  have hk : k ∈ ({k} : Finset (Fin d)) := Finset.mem_singleton_self k
  let u : Fin d → Rb C {k} := C.u {k} k hk
  have hphi : ∀ j, algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j)) = C.t j := by
    intro j
    change phi C _ = _
    simp [phi]
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) := C.chart_surj k
  have hker : RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom =
      Ideal.span (insert (MvPolynomial.X k - 1) (Set.range fun j =>
        MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr j))) -
          MvPolynomial.C (algebraMap (Bp K n d) (Aa C) (MvPolynomial.X (Sum.inr k))) * MvPolynomial.X j)) := by
    simp only [hphi]
    exact C.chart_ker k
  have huk : u k = 1 := by
    have hm : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) (Aa C)) ∈
        RingHom.ker (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u).toRingHom := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_insert _ _)
    have h0 : (MvPolynomial.aeval (R := Aa C) (S₁ := Rb C {k}) u) (MvPolynomial.X k - 1) = 0 := hm
    simpa [sub_eq_zero] using h0
  have htu : ∀ j, toR C {k} (C.t j) = toR C {k} (C.t k) * C.u {k} k hk j := fun j => C.t_eq {k} k hk j
  let w : E n d → C.R {k} := Sum.elim (fun l => toR C {k} (C.x l))
    (fun j => if j = k then toR C {k} (C.t k) else C.u {k} k hk j)
  let Ψ : Bp K n d ≃ₐ[K] R0 K n d {k} := AlgEquiv.ofBijective _ (ChartBij.chart_bijective (K := K) (n := n) k)
  let θ : R0 K n d {k} →ₐ[K] C.R {k} := (MvPolynomial.aeval w).comp Ψ.symm.toAlgHom
  have hθw : ∀ e, θ (mon K (wv k e) (wv_mem hk e)) = w e := by
    intro e
    have h1 : mon K (wv k e) (wv_mem hk e) = Ψ (MvPolynomial.X e) := by simp [Ψ]
    change MvPolynomial.aeval w (Ψ.symm _) = _
    rw [h1, AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]
  have hθr : ∀ j, θ (mon K (ratE k j) (ratE_mem hk j)) = C.u {k} k hk j := by
    intro j
    by_cases h : j = k
    · subst h
      rw [mon_eq_one _ (by simp [ratE]), map_one]
      exact huk.symm
    · have h1 := hθw (Sum.inr j)
      have h2 : wv k (Sum.inr j) = (ratE k j : Gam n d) := by simp [wv, h]
      rw [mon_congr _ (ratE_mem hk j) h2] at h1
      simpa [w, h] using h1
  have hθ : ∀ b, θ (poly n K {k} b) = toR C {k} (phi C b) := by
    have e : θ.comp (poly n K {k}) = (toR C {k}).comp (phi C) := by
      apply MvPolynomial.algHom_ext
      rintro (l | j)
      · have h1 := hθw (Sum.inl l)
        simpa [poly_X, phi, w, wv] using h1
      · have h1 := hθw (Sum.inr k)
        have h2 : wv k (Sum.inr k) = (oneE (Sum.inr k) : Gam n d) := by simp [wv]
        rw [mon_congr _ (oneE_mem {k} _) h2] at h1
        have h3 : mon K (oneE (Sum.inr j) : Gam n d) (oneE_mem {k} _) =
            mon K (oneE (Sum.inr k)) (oneE_mem {k} _) * mon K (ratE k j) (ratE_mem hk j) := by
          rw [mon_mul]
          exact mon_congr _ _ (by simp [ratE])
        simp only [AlgHom.comp_apply, poly_X, phi, MvPolynomial.aeval_X, Sum.elim_inr]
        rw [h3, map_mul, h1, hθr, htu j]
        simp [w]
    exact fun b => DFunLike.congr_fun e b
  refine ⟨θ, hθ, hθr, ?_⟩
  let θ' : R0 K n d {k} →ₐ[Bp K n d] Rb C {k} := { θ.toRingHom with commutes' := fun b => hθ b }
  have hadj : Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := (ChartBij.chart_bijective (K := K) (n := n) k).2 y
    induction p using MvPolynomial.induction_on with
    | C c =>
      have : MvPolynomial.aeval (fun e : E n d => mon K (wv k e) (wv_mem hk e)) (MvPolynomial.C c : Bp K n d) =
          algebraMap (Bp K n d) (R0 K n d {k}) (MvPolynomial.C c) := by
        rw [algebraMap_cone_ring]
        simp [poly]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hp hq
    | mul_X p e hp =>
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      rw [MvPolynomial.aeval_X]
      have hpoly : ∀ e' : E n d, mon K (oneE e') (oneE_mem {k} e') ∈
          Algebra.adjoin (Bp K n d) (Set.range fun j => mon K (ratE k j) (ratE_mem hk j) : Set (R0 K n d {k})) := by
        intro e'
        rw [← poly_X, ← algebraMap_cone_ring]
        exact Subalgebra.algebraMap_mem _ _
      rcases e with l | j
      · exact hpoly _
      · by_cases h : j = k
        · subst h
          rw [mon_congr _ (oneE_mem {j} _) (by simp [wv] : wv j (Sum.inr j) = (oneE (Sum.inr j) : Gam n d))]
          exact hpoly _
        · rw [mon_congr _ (ratE_mem hk j) (by simp [wv, h] : wv k (Sum.inr j) = (ratE k j : Gam n d))]
          exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hbase := isBaseChange_of_presentation (B := Bp K n d) (A := Aa C) (P := R0 K n d {k}) (Q := Rb C {k}) θ' u
    (fun j => mon K (ratE k j) (ratE_mem hk j)) k (fun j => MvPolynomial.X (Sum.inr j)) hθr hsurj hker
    (mon_eq_one _ (by simp [ratE]))
    (fun j => by
      simp only [algebraMap_cone_ring, poly_X]
      rw [mon_mul]
      exact mon_congr _ _ (by simp [ratE]))
    hadj
  exact hbase

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaOne
end
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem baseChange_loc {B A P P' Q Q' : Type} [CommRing B] [CommRing A] [CommRing P] [CommRing P'] [CommRing Q]
    [CommRing Q'] [Algebra B A] [Algebra B P] [Algebra B P'] [Algebra B Q] [Algebra B Q'] [Algebra A Q] [Algebra A Q']
    [IsScalarTower B A Q] [IsScalarTower B A Q']
    (i : P →+* P') (r : Q →+* Q') (t₁ : P →+* Q) (t : P' →+* Q') (c : P)
    (hi : ∀ b, i (algebraMap B P b) = algebraMap B P' b)
    (hr : ∀ a, r (algebraMap A Q a) = algebraMap A Q' a)
    (ht₁ : ∀ b, t₁ (algebraMap B P b) = algebraMap B Q b)
    (ht : ∀ b, t (algebraMap B P' b) = algebraMap B Q' b)
    (hcomm : ∀ x, t (i x) = r (t₁ x))
    (hP : letI := i.toAlgebra; IsLocalization.Away c P')
    (hQ : letI := r.toAlgebra; IsLocalization.Away (t₁ c) Q')
    (f₁ : P →ₗ[B] Q) (hf₁ : ∀ x, f₁ x = t₁ x) (f : P' →ₗ[B] Q') (hf : ∀ x, f x = t x)
    (h : IsBaseChange A f₁) : IsBaseChange A f := by
  letI a1 : Algebra P P' := i.toAlgebra
  letI a2 : Algebra Q Q' := r.toAlgebra
  letI a3 : Algebra P Q := t₁.toAlgebra
  letI a4 : Algebra P' Q' := t.toAlgebra
  letI a5 : Algebra P Q' := (t.comp i).toAlgebra
  haveI : IsScalarTower B P P' := .of_algebraMap_eq fun b => (hi b).symm
  haveI : IsScalarTower B P Q := .of_algebraMap_eq fun b => (ht₁ b).symm
  haveI : IsScalarTower B P' Q' := .of_algebraMap_eq fun b => (ht b).symm
  haveI : IsScalarTower B P Q' := .of_algebraMap_eq fun b => by
    change _ = t (i _)
    rw [hi, ht]
  haveI : IsScalarTower P P' Q' := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower P Q Q' := .of_algebraMap_eq fun x => hcomm x
  haveI : IsScalarTower A Q Q' := .of_algebraMap_eq fun a => (hr a).symm
  haveI : IsScalarTower B Q Q' := .of_algebraMap_eq fun b => by
    rw [IsScalarTower.algebraMap_apply B A Q, IsScalarTower.algebraMap_apply B A Q']
    exact (hr _).symm
  have e1 : f₁ = (IsScalarTower.toAlgHom B P Q).toLinearMap := LinearMap.ext hf₁
  have p1 : Algebra.IsPushout B A P Q := ⟨by rw [← e1]; exact h⟩
  haveI p2 : Algebra.IsPushout B P A Q := p1.symm
  haveI : IsLocalization.Away c P' := hP
  have hQ' : IsLocalization (Algebra.algebraMapSubmonoid Q (Submonoid.powers c)) Q' := by
    have e : Algebra.algebraMapSubmonoid Q (Submonoid.powers c) = Submonoid.powers (t₁ c) := by
      simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      rfl
    rw [e]
    exact hQ
  have p3 : Algebra.IsPushout P Q P' Q' := (Algebra.isLocalization_iff_isPushout (Submonoid.powers c) P').1 hQ'
  have p4 : Algebra.IsPushout P P' Q Q' := p3.symm
  have p5 : Algebra.IsPushout B P' A Q' := (Algebra.IsPushout.comp_iff B P A Q).2 p4
  have e2 : f = (IsScalarTower.toAlgHom B P' Q').toLinearMap := LinearMap.ext hf
  rw [e2]
  exact p5.symm.out

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_congr {M : AddSubmonoid (Gam n d)} {g g' : Gam n d} (e : g = g') (hg : g ∈ M) (hg' : g' ∈ M) :
    mon K g hg = mon K g' hg' := by
  subst e
  rfl

theorem mon_sum {ι : Type} {M : AddSubmonoid (Gam n d)} (s : Finset ι) (g : ι → Gam n d) (hg : ∀ j, g j ∈ M) :
    mon K (∑ j ∈ s, g j) (sum_mem fun j _ => hg j) = ∏ j ∈ s, mon K (g j) (hg j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact mon_congr (K := K) Finset.sum_empty _ M.zero_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, mon_mul]
    exact mon_congr (Finset.sum_insert ha) _ _

def cE (S : Finset (Fin d)) (k : Fin d) : Gam n d := ∑ j ∈ S, ratE k j

theorem cE_mem (S : Finset (Fin d)) (k : Fin d) : cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  sum_mem fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cE_mem {S : Finset (Fin d)} (k : Fin d) : -cE S k ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have e : -cE S k = ∑ j ∈ S, (ratE j k : Gam n d) := by
    simp [cE, ratE, ← Finset.sum_neg_distrib]
  rw [e]
  exact sum_mem fun j hj => ratE_mem hj k

theorem one_le_cE {S : Finset (Fin d)} {k j : Fin d} (hj : j ∈ S) (hne : j ≠ k) :
    1 ≤ (cE S k : Gam n d) (Sum.inr j) := by
  have : (cE S k : Gam n d) (Sum.inr j) = 1 := by
    simp [cE, ratE, oneE, Finset.sum_apply, Pi.single_apply, hj, hne]
  exact this.ge

theorem exists_add_nsmul_mem {S : Finset (Fin d)} (k : Fin d) (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • cE S k ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  have hc := cE_mem (n := n) S k
  have hN := (cone {k} : AddSubmonoid (Gam n d)).nsmul_mem hc
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · exact add_nonneg (hg.1 l) ((hN _).1 l)
  · have hne : j ≠ k := fun h => hj (h ▸ Finset.mem_singleton_self k)
    by_cases hjS : j ∈ S
    · have h1 := one_le_cE (n := n) hjS hne
      have h2 : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
        Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      show 0 ≤ g (Sum.inr j) + (∑ j, (g (Sum.inr j)).natAbs) • (cE S k : Gam n d) (Sum.inr j)
      rw [nsmul_eq_mul]
      have h3 : -g (Sum.inr j) ≤ ((g (Sum.inr j)).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact neg_le_abs _
      have h4 : ((g (Sum.inr j)).natAbs : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
      have h5 : (0 : ℤ) ≤ ((∑ j, (g (Sum.inr j)).natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
      nlinarith
    · exact add_nonneg (hg.2.1 j hjS) ((hN _).2.1 j hj)
  · rw [tdeg_add]
    exact add_nonneg hg.2.2 (hN _).2.2

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc

theorem theta_loc : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) (S : Finset (Fin d)) (k : Fin d) (hk : k ∈ S) (θ₁ : R0 K n d {k} →ₐ[K] C.R {k}) (hθ₁ : ∀ b, θ₁ (poly n K {k} b) = toR C {k} (phi C b)), (∀ j, θ₁ (mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j)) = C.u {k} k (Finset.mem_singleton_self k) j) → IsBaseChange (Aa C) (thetaLin C θ₁ hθ₁) → ∃ (θ : R0 K n d S →ₐ[K] C.R S) (hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b)), IsBaseChange (Aa C) (thetaLin C θ hθ) := by
  intro K _ n d A _ _ C S k hk θ₁ hθ₁ hu hbc
  have hsk : ({k} : Finset (Fin d)) ⊆ S := Finset.singleton_subset_iff.2 hk
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S := cone_mono hsk
  have hc := cE_mem (n := n) S k
  have hP := Away.isLocalization_away (K := K) hle (cE S k) hc (neg_cE_mem k)
    (fun g hg => exists_add_nsmul_mem k g hg)
  have hθc : θ₁ (mon K (cE S k) hc) = ∏ j ∈ S, C.u {k} k (Finset.mem_singleton_self k) j := by
    have e : mon K (cE S k) hc = ∏ j ∈ S, mon K (ratE k j) (ratE_mem (Finset.mem_singleton_self k) j) :=
      mon_sum S _ _
    rw [e, map_prod]
    exact Finset.prod_congr rfl fun j _ => hu j
  letI aP : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  letI aQ : Algebra (C.R {k}) (C.R S) := (C.res hsk).toRingHom.toAlgebra
  haveI hP' : IsLocalization.Away (mon K (cE S k) hc) (R0 K n d S) := hP
  have hQ : IsLocalization.Away (θ₁ (mon K (cE S k) hc)) (C.R S) := by
    rw [hθc]
    exact C.loc S k hk
  have hunit : IsUnit (((C.res hsk).toRingHom.comp θ₁.toRingHom) (mon K (cE S k) hc)) :=
    IsLocalization.Away.algebraMap_isUnit (S := C.R S) (θ₁ (mon K (cE S k) hc))
  let T : R0 K n d S →+* C.R S := IsLocalization.Away.lift (mon K (cE S k) hc) hunit
  have hT : ∀ x, T (incl hle x) = C.res hsk (θ₁ x) := fun x =>
    IsLocalization.Away.lift_eq (mon K (cE S k) hc) hunit x
  let θ : R0 K n d S →ₐ[K] C.R S :=
    { T with
      commutes' := fun r => by
        have e : algebraMap K (R0 K n d S) r = incl hle (algebraMap K (R0 K n d {k}) r) :=
          ((incl (K := K) hle).commutes r).symm
        change T _ = _
        rw [e, hT, θ₁.commutes, (C.res hsk).commutes] }
  have hθT : ∀ x, θ x = T x := fun _ => rfl
  have hθ : ∀ b, θ (poly n K S b) = toR C S (phi C b) := fun b => by
    rw [hθT, ← incl_poly hsk, hT, hθ₁, res_toR]
  refine ⟨θ, hθ, ?_⟩
  exact baseChange_loc (A := Aa C) (Q := Rb C {k}) (Q' := Rb C S)
    (incl (K := K) hle).toRingHom (C.res hsk).toRingHom θ₁.toRingHom T (mon K (cE S k) hc)
    (fun b => incl_poly hsk b) (fun a => res_toR C hsk a) hθ₁ hθ hT hP hQ
    (thetaLin C θ₁ hθ₁) (fun _ => rfl) (thetaLin C θ hθ) (fun _ => rfl) hbc

end GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaLoc
end
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.exP_of_compatible_equiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.exP_of_addEquiv <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.finset_system_injective_extension : ∀ {K : Type} [CommRing K] {ι : Type} [DecidableEq ι] [Fintype ι] {W : Type} [AddCommGroup W] [Module K W] {Λ : Type} (b : Module.Basis Λ K W) (good' : Λ → Prop) (T : Λ → Finset ι), (∀ l, good' l → T l ≠ Finset.univ) → ∀ (M : Finset ι → Type) [∀ S, AddCommGroup (M S)] (r : ∀ {S S' : Finset ι}, S ⊆ S' → M S → M S') (j : ∀ S, M S →+ W), (∀ S, Function.Injective (j S)) → (∀ {S S' : Finset ι} (h : S ⊆ S') x, j S' (r h x) = j S x) → (∀ S w, (∃ x, j S x = w) ↔ w ∈ Submodule.span K (b '' {l | good' l ∧ T l ⊆ S})) → ExP M r := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.Exc.exP_of_basis <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.pm_exactness_of_exP : ∀ {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] (P : PM.{0} R ι), ExP P.M (fun h x => P.res h x) → P.Ex := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ex_of_exP <;> assumption)
end
