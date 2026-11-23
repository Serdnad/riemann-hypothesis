module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle006
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle007
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Mathlib.RingTheory.LaurentSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory.MaxCuspKilled

open MeasureTheory GlobalTheory.TorusFourier

noncomputable def dotForm {ι : Type} [Fintype ι] (c : ℝ) (v : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun t := c * ∑ k, v k * t k
  map_add' s t := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a s := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem dotForm_apply {ι : Type} [Fintype ι] (c : ℝ) (v t : ι → ℝ) :
    dotForm c v t = c * ∑ k, v k * t k := rfl

theorem coefFn_eq_cubeCoeff {Ω : Type} {N : ℕ} (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ)
    (P : Ω → ℂ) (x : Ω) :
    coefFn act ph P x =
      cubeCoeff (Pi.basisFun ℝ (Fin N)) (fun t => P (act t x)) (dotForm 1 ph) := by
  have h : ∀ t : Fin N → ℝ, ∑ i, t i • Pi.basisFun ℝ (Fin N) i = t := fun t =>
    (Pi.basisFun ℝ (Fin N)).sum_repr t
  unfold coefFn cubeCoeff cube
  rw [← Set.pi_univ_Icc]
  simp only [h]
  congr 1
  funext t
  have hphase : (∑ k, t k * ph k) = ∑ k, ph k * t k :=
    Finset.sum_congr rfl fun k _ => mul_comm (t k) (ph k)
  simp only [integrand, chr, eNeg, dotForm_apply, one_mul, hphase]

theorem herm_comb {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ} {X : Data E r}
    (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  apply GlobalTheory.CuspFlow.herm_comb_eq_zero <;> assumption

theorem coefFn_eq_zero_of_killed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r), (∀ cu : CuspFD X ρ, ∃ bs, IsZBasis X cu bs) → ∀ (la : Wt X.Ψ r), (∀ (cu : CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E), β ∈ zGam X cu → ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β → X.χ la γ = 1) → ∀ (c : ℝ) (P : Frame X.Ψ r → ℂ), P ∈ X.SSgt la c → ∀ (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsExpoFD X cu χ → KilledFD X cu χ c → ∀ x ∈ X.dom, coefFn (zAct X cu) (phZ X cu χ) P x = 0 := by
  intro E _ _ _ r ρ X hbas la hchi c P hP cu χ hχ hK x hx
  obtain ⟨η, hη0, hηΛ, hηc⟩ := hK
  have hb : IsZBasis X cu (zBas X cu) := Classical.epsilon_spec (hbas cu)
  have hsec : X.IsSec la P := hP.1.1.1
  have hdom : ∀ u, zAct X cu u x ∈ X.dom := fun u =>
    zAct_mem_dom X cu (zBas_skew X cu (hbas cu)) u x hx
  obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.T.cuspFlow_eq_torusAction E r ρ X cu hb η hηΛ
  have hiso : X.IsIso (∑ a, η a • cu.e a) :=
    ⟨hηΛ, herm_comb cu η, fun h => hη0 (funext (Fintype.linearIndependent_iff.1 cu.ind η h))⟩
  set ν : X.Ψ → ℝ := fun τ => (τ.1 (hq χ η)).re with hν
  set g : (Fin (nZ X ρ) → ℝ) → ℂ := fun t => P (zAct X cu t x) with hg
  have hgc : Continuous g := hsec.1.continuousOn.comp_continuous (continuous_zAct X cu x) hdom
  have hper : ∀ l : Fin (nZ X ρ) → ℝ, (∀ k, ∃ z : ℤ, l k = z) → ∀ u, g (u + l) = g u := by
    intro l hl u
    choose n hn using hl
    have : l = fun i => (n i : ℝ) := funext hn
    rw [this]
    exact maxCuspsA_periodic X cu hb la (hchi cu) P hsec x hx u n
  have hcomp : dotForm 1 (phZ X cu χ) ∘ₗ L = dotForm 2 ν := by
    refine LinearMap.ext fun s => ?_
    rw [LinearMap.comp_apply, dotForm_apply, dotForm_apply, one_mul, hL2 χ hχ.1 s]
  have hfreq : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    intro p hp
    choose n hn using hL3 la p hp
    choose m hm using hχ.2
    refine ⟨∑ k, m k * n k, ?_⟩
    rw [← hL2 χ hχ.1 p]
    simp only [hn, hm]
    push_cast
    rfl
  have hex := PeriodLatticeCountable.fd_exists X la
  obtain ⟨-, hD, h0, h1⟩ := hex.choose_spec
  obtain ⟨H₁, -, -⟩ := partialCoeff_spec_cube (Pi.basisFun ℝ (Fin (nZ X ρ))) hD h0.ne' h1.ne L hgc
    (fun i => hper _ fun k => ⟨if k = i then 1 else 0, by
      by_cases h : k = i <;> simp [h]⟩)
    (fun l hl => hper _ (hL3 la l hl))
  obtain ⟨-, -, -, B⟩ := H₁ (dotForm 2 ν) hfreq
  rw [coefFn_eq_cubeCoeff]
  refine B.1 ?_ _ (fun i => ?_) hcomp
  · funext b
    have h := hP.2 _ hiso ν hηc _ (hdom b)
    rw [Data.fj, if_pos hfreq, dite_eq_left hex] at h
    rw [partialCoeff, coeff_eq, Pi.zero_apply, ← h]
    congr 2
    funext s
    rw [hL1, maxCuspsA_zAct_add, add_comm (L s), dotForm_apply]
    congr 2
    push_cast
    ring
  · obtain ⟨z, hz⟩ := hχ.2 i
    exact ⟨z, by simp [dotForm_apply, Pi.single_apply, hz]⟩

end GlobalTheory.MaxCuspKilled
end

section

open NumberField

namespace GlobalTheory.HomTrace

lemma finrank_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℂ (X →+ ℂ) = Module.finrank ℤ X := by
  rw [(addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).finrank_eq, Module.finrank_linearMap]
  simp

lemma finite_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.Finite ℂ (X →+ ℂ) :=
  Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).symm

theorem trace_eq_finrank_mul_sum (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : 𝓞 E) (f : (X →+ ℂ) →ₗ[ℂ] (X →+ ℂ))
    (hf : ∀ l x, f l x = l (a • x)) :
    LinearMap.trace ℂ (X →+ ℂ) f = (Module.finrank (𝓞 E) X : ℂ) * ∑ τ : E →+* ℂ, τ (a : E) := by
  classical
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X with hr
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) hr.le
  let j : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) v
  let F : Submodule (𝓞 E) X := Submodule.span (𝓞 E) (Set.range v)
  have hF : Module.finrank (𝓞 E) F = r := by simpa using finrank_span_eq_card hv
  have h0 : Module.finrank (𝓞 E) (X ⧸ F) = 0 := by
    have := F.finrank_quotient_add_finrank
    omega
  have htor : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ ∃ y, j y = n • x := by
    intro x
    rw [Module.finrank_eq_zero_iff] at h0
    obtain ⟨c, hc, hx⟩ := h0 (Submodule.Quotient.mk x)
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc)
    refine ⟨n, hn, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    have h1 : n • x ∈ F := by
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul]
      exact F.smul_mem _ hx
    rw [show F = LinearMap.range j from (Fintype.range_linearCombination _ _).symm] at h1
    exact h1
  let R : (X →+ ℂ) →ₗ[ℂ] ((Fin r → 𝓞 E) →+ ℂ) :=
    { toFun := fun l => l.comp j.toAddMonoidHom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ l y, R l y = l (j y) := fun _ _ => rfl
  have hinj : Function.Injective R := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro l hl
    ext x
    obtain ⟨n, hn, y, hy⟩ := htor x
    have h1 : l (j y) = 0 := by rw [← hR, hl]; rfl
    rw [hy, map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn)
  have := finite_hom X
  have := finite_hom (Fin r → 𝓞 E)
  have hdY : Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) = r * Module.finrank ℚ E := by
    rw [finrank_hom, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  have hdim : Module.finrank ℂ (X →+ ℂ) = Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) := by
    rw [hdY, finrank_hom, finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank, mul_comm]
  let e := LinearMap.linearEquivOfInjective R hinj hdim
  let g : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hg : Function.Injective g := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp g hg
  let w : Fin r × (E →+* ℂ) → ((Fin r → 𝓞 E) →+ ℂ) := fun p =>
    ((p.2.comp (algebraMap (𝓞 E) E)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ => 𝓞 E) p.1)
  have hw : ∀ p y, w p y = p.2 (y p.1 : E) := fun _ _ => rfl
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨i, τ⟩
    refine Fintype.linearIndependent_iff.1 hli (fun φ => c (i, φ)) ?_ τ
    funext y
    have h1 := DFunLike.congr_fun hc (Pi.single i y)
    rw [AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i] at h1
    · simpa [hw, g] using h1
    · intro k _ hk
      simp [hw, Pi.single_eq_of_ne hk]
    · simp
  let b := basisOfLinearIndependentOfCardEqFinrank' w hwli (by
    rw [hdY, Fintype.card_prod, Fintype.card_fin, Embeddings.card])
  let c := b.map e.symm
  have hc : ∀ p, R (c p) = w p := fun p => by
    have : e (c p) = b p := by simp [c]
    rw [← show b p = w p by simp [b], ← this]; rfl
  have hfc : ∀ p, f (c p) = p.2 (a : E) • c p := fun p => by
    apply hinj
    refine AddMonoidHom.ext fun y => ?_
    rw [map_smul, hR, hf, ← j.map_smul, ← hR, hc, AddMonoidHom.smul_apply, hw, hw]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℂ c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hfc, Fintype.sum_prod_type]

end GlobalTheory.HomTrace
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries

namespace GlobalTheory.HolomorphicArc

theorem map_nsmul_eq_pow {L G : Type} [AddCommGroup L] [Group G] (f : L → G) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f (n • a) = f a ^ n := by
  induction n with
  | zero =>
    have h := hf 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem nsmul_mem (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  have h : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]
    exact Ideal.mem_span_singleton_self _
  have h' : (l.M : 𝓞 E) ∈ l.Mb := Ideal.mul_le_left h
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul h' Submodule.mem_top

theorem over_of_generic {S : Scheme.{0}} {k : Type} [CommRing k] (s : S ⟶ Sp k) (σ : k →+* ℂ)
    (R : Subalgebra ℂ ℂ⸨X⸩) (y : Sp R ⟶ S) (ev : R →ₐ[ℂ] ℂ)
    (h : (spMap R.val.toRingHom ≫ y) ≫ s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ)) :
    (spMap ev.toRingHom ≫ y) ≫ s = spMap σ := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (y ≫ s)
  have h₁ : y ≫ s = spMap φ.hom := hφ.symm
  rw [Category.assoc, h₁, ← spMap_comp] at h ⊢
  have h₂ := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  congr 1
  ext x
  have h₃ : φ.hom x = algebraMap ℂ R (σ x) := Subtype.ext (DFunLike.congr_fun h₂ x)
  exact (congrArg ev h₃).trans (ev.commutes _)

theorem isHolTo_halfPlane_mono {X : Scheme.{0}} {y : ℂ → (Sp ℂ ⟶ X)} {T T' : ℝ} (h : T ≤ T')
    (hol : IsHolTo {w : ℂ | T < w.im} y) : IsHolTo {w : ℂ | T' < w.im} y := by
  intro U f
  have e : {b | b ∈ {w : ℂ | T' < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} =
      {w : ℂ | T' < w.im} ∩ {b | b ∈ {w : ℂ | T < w.im} ∧ ⊤ ≤ y b ⁻¹ᵁ U} :=
    Set.ext fun b => ⟨fun hb => ⟨hb.1, h.trans_lt hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  rw [e]
  exact ⟨(isOpen_lt continuous_const Complex.continuous_im).inter (hol U f).1,
    (hol U f).2.mono Set.inter_subset_right⟩

end GlobalTheory.HolomorphicArc
end
end
