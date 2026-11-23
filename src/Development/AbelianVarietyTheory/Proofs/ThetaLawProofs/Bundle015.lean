module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.SpGenStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Blocks
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec
import ReciprocityTheory.ThetaQuasiPeriods.Bundle001
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.KeyPow

theorem theta_sq_congr_mod_two {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
  rw [theta_sq_red k k', theta_sq_red m m', funext h, funext h']

theorem ThetaLaw.congr_target {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by
  obtain ⟨c, hc, hlaw⟩ := hl
  exact ⟨c, hc, fun τ hτ z => by rw [theta_sq_congr_mod_two h h']; exact hlaw τ hτ z⟩

theorem thetaLaw_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) (n n' : Fin g → ℤ) :
    ThetaLaw g (spTransl S) n n' n (n' - S *ᵥ n - fun i => S i i) := by
  set X : ℂ := -(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) with hX
  refine ⟨eC X ^ 2, ?_, fun τ _ z => ?_⟩
  · rw [← pow_mul, eC_pow]
    have h8 : ((2 * 4 : ℕ) : ℂ) * X = ((-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ fun i => S i i) : ℤ) : ℂ) := by
      have hd : ofIntVec n ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ)) = ((n ⬝ᵥ fun i => S i i : ℤ) : ℂ) := by
        simp [dotProduct, ofIntVec]
      have hd2 : (fun i => ((S i i : ℤ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((S i i : ℤ) : ℂ) := by
        ext i; simp; ring
      rw [hX, ofRealVec_halfVec, Matrix.mulVec_smul, ← ofIntVec_mulVec, smul_dotProduct,
        dotProduct_smul, ofIntVec_dot, hd2, smul_dotProduct, dotProduct_smul, hd]
      simp only [smul_eq_mul]
      push_cast; ring
    rw [h8, eC_int]
  · have hb : halfVec (n' - S *ᵥ n - fun i => S i i) + S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n +
        (fun i => ((S i i : ℤ) : ℝ) / 2) = halfVec n' := by
      rw [mulVec_halfVec]
      ext i; simp only [halfVec, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have he : expArg (spTransl S) τ z = 0 := by simp [expArg, jAut_spTransl, cMat_spTransl]
    rw [hz, he, spAct_spTransl, jAut_spTransl, thetaTranslTau_holds (Fin g) _ _ _ _ S hS, hb,
      mul_pow, det_one, eC_zero]
    ring

theorem thetaLaw_J {g : ℕ} (hInv : InversionStatement) (n n' : Fin g → ℤ) :
    ThetaLaw g (Matrix.J (Fin g) ℤ) n n' (-n') n := by
  set F : ℂ := 2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))
  refine ⟨(-I) ^ g * eC F, ?_, fun τ hτ z => ?_⟩
  · rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, eC_pow]
    have hI : (-I : ℂ) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
    have hF : ((4 : ℕ) : ℂ) * F = ((-(2 * (n' ⬝ᵥ n)) : ℤ) : ℂ) := by
      simp only [F, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
      simp [dotProduct]; ring
    rw [hI, one_pow, one_mul, hF, eC_int]
  · have hsym : τ.IsSymm := hτ.1
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct_eq, jAut_J, nAut_eq, cMat_J]; simp [Matrix.J]
    have htinv : (τ⁻¹)ᵀ = τ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym.eq]
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by rw [zAct, jAut_J, htinv]
    have he : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]; simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by ext i; simp [halfVec]; ring
    rw [hs, hz, he, jAut_J, hInv g _ _ τ hτ z, hneg]
    ring

theorem thetaLaw_generators (hInv : InversionStatement) (g : ℕ) (k k' : Fin g → ℤ) :
    (∀ (S : Matrix (Fin g) (Fin g) ℤ) (n' : Fin g → ℤ), S.IsSymm →
      (∀ i, (2 : ℤ) ∣ (S.mulVec k) i + S i i + k' i - n' i) → ThetaLaw g (spTransl S) k n' k k') ∧
    ThetaLaw g (Matrix.J (Fin g) ℤ) k' k k k' := by
  refine ⟨fun S n' hS hd => (thetaLaw_spTransl S hS k n').congr_target (fun _ => rfl) fun i => ?_,
    (thetaLaw_J hInv k' k).congr_target (fun i => ?_) fun _ => rfl⟩
  · have := hd i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.neg_apply]
    omega

end GlobalTheory.KeyPow
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SectionFn

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem differentiable_of_isFn (hL : L.IsLB) {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) :
    Differentiable ℂ θ := by
  intro z
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hn := (u.hol (L.U i) (s.f i)).1.mem_nhds hi
  have d : DifferentiableOn ℂ (fun w => valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹)
      {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ L.U i} :=
    (u.hol (L.U i) (s.f i)).2.mul ((u.fr_hol i).inv fun w hw => u.fr_ne i w hw)
  refine (d.differentiableAt hn).congr_of_eventuallyEq (Filter.mem_of_superset hn fun w hw => ?_)
  have := u.fr_ne i w hw
  change θ w = valAt' (u.ex w).left (L.U i) (s.f i) * (u.fr i w)⁻¹
  rw [h i w hw]
  field_simp

theorem isThetaFn_of_isFn (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (hAH : u.IsAH Hm χ)
    {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsThetaFn Hm χ 1 θ := by
  refine ⟨differentiable_of_isFn u hL h, fun l z => ?_⟩
  have hper : u.ex (z + l) = u.ex z := by
    rw [u.ex_add, (u.ker l).2 l.2, _root_.mul_one]
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
  have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i := by rwa [hper]
  have h1 := h i z hi
  have h2 := h i (z + l) hi'
  rw [hper, h1, hAH.2.2.2 l i z hi] at h2
  refine mul_right_cancel₀ (u.fr_ne i _ hi') ?_
  rw [← h2, pow_one]
  unfold hermForm
  ring

theorem ne_zero_of_isFn [LocallyOfFiniteType A.hom] {s : L.Sec} {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ)
    {p : A.left} (hp : p ∈ Out.nonzeroLocus s) : θ ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  have hle : A.left.basicOpen (s.f i) ≤ ⊥ := by
    refine ComplexPoints.opens_le_of_complexPoints A.hom _ _ fun y hy hyb => ?_
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk y hy)
    have hzy : (u.ex z).left = y := by rw [hz]; rfl
    subst hzy
    have hne := (top_le_preimage_basicOpen_iff _ _ _).1 hyb
    have hU := top_le_preimage_of_valAt'_ne_zero _ hne
    exact absurd (by simpa using h i z hU) hne
  exact hle hi

end SectionFn

theorem isThetaFn_and_ne_zero_of_isFn :
    ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin x.P.g → ℂ) → ℂ), u.IsAH Hm χ → u.IsFn x.th θ → u.IsThetaFn Hm χ 1 θ ∧ θ ≠ 0 := by
  intro x u Hm χ θ hAH h
  refine ⟨SectionFn.isThetaFn_of_isFn u x.P.isLB hAH h, ?_⟩
  obtain ⟨p, -, hp⟩ := x.th_ne (default : PrimeSpectrum ℂ)
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  exact SectionFn.ne_zero_of_isFn u h hp

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory.GermInterp

theorem isMaximal_of_finite_primes {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) (Q : Ideal R) (hQ : Q.IsPrime) (hI : I ≤ Q) :
    Q.IsMaximal := by
  have hT : {J : Ideal R | Q ≤ J ∧ J.IsMaximal}.Finite := by
    refine (hfin.image PrimeSpectrum.asIdeal).subset ?_
    rintro J ⟨hQJ, hJ⟩
    exact ⟨⟨J, hJ.isPrime⟩, le_trans hI hQJ, rfl⟩
  have hJac : Q.jacobson = Q := IsJacobsonRing.out inferInstance hQ.isRadical
  have hinf : hT.toFinset.inf id ≤ Q := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact hJac.le
  obtain ⟨M, hM, hMQ⟩ := hQ.inf_le'.1 hinf
  rw [Set.Finite.mem_toFinset] at hM
  rw [show Q = M from le_antisymm hM.1 hMQ]
  exact hM.2

theorem eq_of_comap_map_le {R : Type*} [CommRing R] (I : Ideal R)
    (hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal) (P : Ideal R) [hP : P.IsPrime] (hI : I ≤ P)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (M : Ideal R) (hM : M.IsMaximal)
    (h : (I.map (algebraMap R S)).comap (algebraMap R S) ≤ M) : M = P := by
  by_contra hne
  have hMP : ¬ M ≤ P := fun hle => hne (hM.eq_of_le hP.ne_top hle)
  obtain ⟨m, hmM, hmP⟩ := Set.not_subset.1 hMP
  have hmeet : ¬ Disjoint (I : Set R) (↑(M.primeCompl ⊔ Submonoid.powers m) : Set R) := by
    intro hdis
    obtain ⟨Q, hQ, hIQ, hQdis⟩ := Ideal.exists_le_prime_disjoint I _ hdis
    have hQM : Q ≤ M := by
      intro x hx
      by_contra hxM
      exact Set.disjoint_left.1 hQdis hx
        (Submonoid.mem_sup_left (show x ∈ M.primeCompl from hxM))
    have hmQ : m ∉ Q := fun hm =>
      Set.disjoint_left.1 hQdis hm (Submonoid.mem_sup_right (Submonoid.mem_powers m))
    exact hmQ (((hmax Q hQ hIQ).eq_of_le hM.ne_top hQM) ▸ hmM)
  obtain ⟨w, hwI, hwW⟩ := Set.not_disjoint_iff.1 hmeet
  obtain ⟨v, hv, u, hu, rfl⟩ := Submonoid.mem_sup.1 hwW
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hu
  have hunit : IsUnit (algebraMap R S (m ^ k)) :=
    IsLocalization.map_units S (⟨m ^ k, fun h => hmP (hP.mem_of_pow_mem k h)⟩ : P.primeCompl)
  have hvmap : v ∈ (I.map (algebraMap R S)).comap (algebraMap R S) := by
    rw [Ideal.mem_comap]
    have hw := Ideal.mem_map_of_mem (algebraMap R S) hwI
    rw [map_mul] at hw
    exact (Ideal.mul_unit_mem_iff_mem _ hunit).1 hw
  exact hv (h hvmap)

theorem exists_sub_mem_map {R : Type*} [CommRing R] [IsJacobsonRing R] (I : Ideal R)
    (hfin : {P : PrimeSpectrum R | I ≤ P.asIdeal}.Finite) {κ : Type*} [Finite κ] (P : κ → PrimeSpectrum R)
    (hinj : Function.Injective P) (hI : ∀ i, I ≤ (P i).asIdeal) (S : κ → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] [∀ i, IsLocalization.AtPrime (S i) (P i).asIdeal] (a : ∀ i, S i) :
    ∃ r : R, ∀ i, algebraMap R (S i) r - a i ∈ I.map (algebraMap R (S i)) := by
  have hmax : ∀ Q : Ideal R, Q.IsPrime → I ≤ Q → Q.IsMaximal :=
    fun Q hQ hIQ => isMaximal_of_finite_primes I hfin Q hQ hIQ
  let N : κ → Ideal R := fun i => (I.map (algebraMap R (S i))).comap (algebraMap R (S i))
  have key : ∀ i (M : Ideal R), M.IsMaximal → N i ≤ M → M = (P i).asIdeal :=
    fun i M hM hle => eq_of_comap_map_le I hmax (P i).asIdeal (hI i) (S i) M hM hle
  have hcop : Pairwise fun i j => IsCoprime (N i) (N j) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have e1 := key i M hM (le_trans le_sup_left hle)
    have e2 := key j M hM (le_trans le_sup_right hle)
    exact hij (hinj (PrimeSpectrum.ext (e1.symm.trans e2)))
  have hfrac : ∀ i, ∃ x : R, ∃ s : (P i).asIdeal.primeCompl, IsLocalization.mk' (S i) x s = a i := by
    intro i
    obtain ⟨⟨x, s⟩, h⟩ := IsLocalization.mk'_surjective (P i).asIdeal.primeCompl (a i)
    exact ⟨x, s, h⟩
  choose x s hxs using hfrac
  have hinv : ∀ i, ∃ t : R, (s i : R) * t - 1 ∈ N i := by
    intro i
    have hsup : N i ⊔ Ideal.span {(s i : R)} = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
      have e := key i M hM (le_trans le_sup_left hle)
      have hsM : (s i : R) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      rw [e] at hsM
      exact (s i).2 hsM
    have h1 : (1 : R) ∈ N i ⊔ Ideal.span {(s i : R)} := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine ⟨t, ?_⟩
    have e : (s i : R) * t - 1 = -y := by rw [← hyz]; ring
    rw [e]
    exact (N i).neg_mem hy
  choose t ht using hinv
  obtain ⟨z, hz⟩ := Ideal.quotientInfToPiQuotient_surj hcop (fun i => Ideal.Quotient.mk (N i) (x i * t i))
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨r, fun i => ?_⟩
  have hri : r - x i * t i ∈ N i := by
    have e := congrFun hz i
    rw [Ideal.quotientInfToPiQuotient_mk'] at e
    exact Ideal.Quotient.eq.1 e
  have h1 : algebraMap R (S i) r - algebraMap R (S i) (x i * t i) ∈ I.map (algebraMap R (S i)) := by
    rw [← map_sub]
    exact Ideal.mem_comap.1 hri
  have h2 : algebraMap R (S i) (x i * t i) - a i ∈ I.map (algebraMap R (S i)) := by
    rw [← hxs i]
    have hst : algebraMap R (S i) ((s i : R) * t i - 1) ∈ I.map (algebraMap R (S i)) :=
      Ideal.mem_comap.1 (ht i)
    have hspec := IsLocalization.mk'_spec (S i) (x i) (s i)
    have e : algebraMap R (S i) (x i * t i) - IsLocalization.mk' (S i) (x i) (s i) =
        IsLocalization.mk' (S i) (x i) (s i) * algebraMap R (S i) ((s i : R) * t i - 1) := by
      simp only [map_sub, map_mul, map_one]
      linear_combination (-(algebraMap R (S i) (t i))) * hspec
    rw [e]
    exact Ideal.mul_mem_left _ _ hst
  convert Ideal.add_mem _ h1 h2 using 1
  ring

theorem mem_primeIdealOf_iff {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (y : X) (hy : y ∈ V)
    (g : Γ(X, V)) : g ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal ↔ y ∉ X.basicOpen g := by
  have h1 : hV.primeIdealOf ⟨y, hy⟩ ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen g ↔ y ∈ X.basicOpen g := by
    show hV.fromSpec (hV.primeIdealOf ⟨y, hy⟩) ∈ X.basicOpen g ↔ _
    rw [hV.fromSpec_primeIdealOf]
  rw [hV.fromSpec_preimage_basicOpen] at h1
  constructor
  · intro hg hyb
    exact (h1.2 hyb) hg
  · intro hyb
    by_contra hg
    exact hyb (h1.1 hg)

theorem exists_germ_sub_mem : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (a : ∀ y : X, X.presheaf.stalk y), LocallyOfFiniteType p → IsAffineOpen V → Set.Finite {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)} → ∃ r : Γ(X, V), ∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i)) := by
  intro K _ X p V J f a hft hV hfin
  let I : Ideal Γ(X, V) := Ideal.span (Set.range f)
  let Z := {y : X | y ∈ V ∧ ∀ i, y ∉ X.basicOpen (f i)}
  have : Finite Z := hfin.to_subtype
  let P : Z → PrimeSpectrum Γ(X, V) := fun k => hV.primeIdealOf ⟨k.1, k.2.1⟩
  have hIP : ∀ k, I ≤ (P k).asIdeal := by
    intro k
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_primeIdealOf_iff hV k.1 k.2.1 (f i)).2 (k.2.2 i)
  have hinj : Function.Injective P := by
    intro k k' e
    apply Subtype.ext
    have e1 := hV.fromSpec_primeIdealOf ⟨k.1, k.2.1⟩
    have e2 := hV.fromSpec_primeIdealOf ⟨k'.1, k'.2.1⟩
    have e3 : hV.primeIdealOf ⟨k.1, k.2.1⟩ = hV.primeIdealOf ⟨k'.1, k'.2.1⟩ := e
    rw [e3] at e1
    exact e1.symm.trans e2
  have hfinR : {Q : PrimeSpectrum Γ(X, V) | I ≤ Q.asIdeal}.Finite := by
    refine (Set.finite_range P).subset ?_
    intro Q hQ
    have hyV : hV.fromSpec Q ∈ V := hV.range_fromSpec.le ⟨Q, rfl⟩
    have hQeq : hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩ = Q :=
      hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec Q, hyV⟩)
    refine ⟨⟨hV.fromSpec Q, hyV, fun i => ?_⟩, hQeq⟩
    have hfi : f i ∈ (hV.primeIdealOf ⟨hV.fromSpec Q, hyV⟩).asIdeal := by
      rw [hQeq]
      exact hQ (Ideal.subset_span ⟨i, rfl⟩)
    exact (mem_primeIdealOf_iff hV _ hyV (f i)).1 hfi
  have : IsJacobsonRing Γ(Sp K, ⊤) :=
    isJacobsonRing_of_surjective ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.toRingHom,
      RingEquiv.surjective _⟩
  have : IsJacobsonRing Γ(X, V) :=
    RingHom.FiniteType.isJacobsonRing
      (Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp K)) hV (by intro x _; simp))
  letI alg : ∀ k : Z, Algebra Γ(X, V) (X.presheaf.stalk k.1) :=
    fun k => TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨k.1, k.2.1⟩
  have loc : ∀ k : Z, IsLocalization.AtPrime (X.presheaf.stalk k.1) (P k).asIdeal :=
    fun k => hV.isLocalization_stalk ⟨k.1, k.2.1⟩
  obtain ⟨r, hr⟩ := exists_sub_mem_map I hfinR P hinj hIP (fun k => X.presheaf.stalk k.1) (fun k => a k.1)
  refine ⟨r, fun y hy hz => ?_⟩
  let k : Z := ⟨y, hy, hz⟩
  have hgs : ∀ g : Γ(X, V), gs (𝟙 X) y V g = algebraMap Γ(X, V) (X.presheaf.stalk k.1) g := by
    intro g
    rw [gs_eq (𝟙 X) y V hy g]
    rfl
  have hk := hr k
  rw [Ideal.map_span, ← Set.range_comp] at hk
  have e : (fun i => gs (𝟙 X) y V (f i)) = (algebraMap Γ(X, V) (X.presheaf.stalk k.1)) ∘ f := by
    funext i
    exact hgs (f i)
  rw [e, hgs r]
  exact hk

end GlobalTheory.GermInterp
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

namespace GlobalTheory

private theorem gs_id_eq_germ (X : Scheme.{0}) (V : X.Opens) (y : X) (hy : y ∈ V) (a : Γ(X, V)) :
    gs (𝟙 X) y V a = X.presheaf.germ V y hy a := by
  rw [gs_eq (𝟙 X) y V hy a]
  rfl

theorem mem_span_of_forall_germ_mem_span : ∀ (X : Scheme.{0}) (V : X.Opens) (J : Type) (f : J → Γ(X, V)) (r : Γ(X, V)), IsAffineOpen V → (∀ y : X, y ∈ V → (∀ i, y ∉ X.basicOpen (f i)) → gs (𝟙 X) y V r ∈ Ideal.span (Set.range fun i => gs (𝟙 X) y V (f i))) → r ∈ Ideal.span (Set.range f) := by
  intro X V J f r hV h
  rw [hV.mem_ideal_iff]
  intro y hy
  rw [Ideal.map_span, ← Set.range_comp]
  by_cases hz : ∀ i, y ∉ X.basicOpen (f i)
  · have hr := h y hy hz
    simp only [gs_id_eq_germ X V y hy] at hr
    exact hr
  · simp only [not_forall, not_not] at hz
    obtain ⟨i, hi⟩ := hz
    rw [X.mem_basicOpen (f i) y hy] at hi
    have hmem : X.presheaf.germ V y hy (f i) ∈ Ideal.span (Set.range (⇑(X.presheaf.germ V y hy).hom ∘ f)) :=
      Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_of_isUnit_mem _ hmem hi]
    trivial

end GlobalTheory
end
