module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import GroundTheory.AutomorphicForms.SatakeNormalized
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle279
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle280
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.RelOpsLeaf

section Linear

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem eq_det_smul_one (hV : finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  have hm := LinearMap.charpoly_monic f
  have hd : f.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, hV]
  have h1 := hm.eq_X_add_C hd
  have h2 := LinearMap.aeval_self_charpoly f
  obtain ⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by
    refine ⟨-f.charpoly.coeff 0, ?_⟩
    rw [h1, map_add (f := _), aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  subst ht
  rw [LinearMap.det_smul, hV, pow_one]
  simp

theorem charpoly_smul_eq_scaleRoots (f : Module.End ℂ V) {t : ℂ} (ht : t ≠ 0) :
    (t • f).charpoly = f.charpoly.scaleRoots t := by
  refine Polynomial.funext fun z => ?_
  have h0 : t * (z / t) = z := by field_simp
  have h1 := scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t
  simp only [RingHom.id_apply, h0, eval₂_id] at h1
  rw [h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree,
    ← LinearMap.det_smul]
  congr 1
  rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]

theorem charpoly_map_one (hV' : finrank ℂ V' = 1) (f : Module.End ℂ V) :
    (TensorProduct.map f (1 : Module.End ℂ V')).charpoly = f.charpoly := by
  let e : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])
  let F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [F]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← LinearEquiv.charpoly_conj F]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := F.surjective v
  simp [LinearEquiv.conj_apply, key]

end Linear

theorem pow_of_mul_eq_pow {p q : ℂ[X]} {m n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m) (hqd : q.natDegree = n) (h : p * q = (X - 1) ^ (m + n)) :
    p = (X - 1) ^ m ∧ q = (X - 1) ^ n := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at h ⊢
  have key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree := by
    intro r hr hd
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd
    have h1 := eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi
    have h2 : r.natDegree = i := by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [h2]
    exact h1
  subst hpd hqd
  exact ⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩

section Rel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_char_of_lpDim_eq_one (c : WD h) (hc : c.lpDim = 1) :
    ∃ χ : ↥(Weil h) →* ℂˣ, ∀ (x : WD h) (g : ↥(Weil h)),
      (x.lpChar c).charPol g = (x.charPol g).scaleRoots (χ g : ℂ) := by
  induction c using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk] at hc
    let f : ↥(Weil h) →* ℂ := (LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ
    refine ⟨f.toHomUnits, fun x g => ?_⟩
    induction x using WD.ind with
    | hP n a =>
      have hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ)) := by
        rw [MonoidHom.coe_toHomUnits]
        exact eq_det_smul_one hc (b.ρ g)
      rw [WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb,
        TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _),
        charpoly_map_one hc]

end Rel

end GlobalTheory.CompanionTheory.RelOpsLeaf
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.PDAcyc

variable {B : Type} [CommRing B] {J : Ideal B}

theorem le_fil_one (δ : DividedPowers J) : J ≤ fil δ 1 := by
  intro j hj
  refine Ideal.subset_span ⟨[(1, j)], by simpa using hj, by simp, by simp [δ.dpow_one hj]⟩

theorem algebraMap_mem_ext (Q : PDPoly B) {j : B} (hj : j ∈ J) :
    algebraMap B Q.P j ∈ Q.ext J :=
  Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hj)

theorem e_one_mem_ext (Q : PDPoly B) : Q.e 1 ∈ Q.ext J :=
  Ideal.mem_sup_right (Ideal.subset_span ⟨0, rfl⟩)

theorem map_e {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {μ q : B} (hμ : μ ∈ J) (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P μ + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) = ∑ j ∈ Finset.range (k + 1), (δ.dpow j μ * q ^ (k - j)) • Q.e (k - j) := by
  have he1 : Q.e 1 ∈ Q.ext J := e_one_mem_ext Q
  have hm : algebraMap B Q.P μ ∈ Q.ext J := algebraMap_mem_ext Q hμ
  have hq : algebraMap B Q.P q * Q.e 1 ∈ Q.ext J := Ideal.mul_mem_left _ _ he1
  have h0 : g (Q.e k) = η.dpow k (g (Q.e 1)) := by
    rw [hgd.dpow_comp _ he1, hS.var]
  rw [h0, h1, η.dpow_add hm hq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b ↦ η.dpow a (algebraMap B Q.P μ) * η.dpow b (algebraMap B Q.P q * Q.e 1))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [η.dpow_mul he1, hS.var, hS.dp.dpow_comp _ hμ, Algebra.smul_def, map_mul, map_pow]
  ring

noncomputable def qDer (Q : PDPoly B) (q : B) (ν : ℕ → B) : Q.P →ₗ[B] Q.P :=
  Q.e.constr B fun k ↦ (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
    ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1))

theorem qDer_e (Q : PDPoly B) (q : B) (ν : ℕ → B) (k : ℕ) :
    qDer Q q ν (Q.e k) = (∑ i ∈ Finset.range k, q ^ i) • Q.e k +
      ∑ m ∈ Finset.range k, (ν (m + 1) * q ^ (k - (m + 1))) • Q.e (k - (m + 1)) := by
  simp only [qDer, Module.Basis.constr_basis]

theorem map_e_sub {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (k : ℕ) :
    g (Q.e k) - Q.e k = (q - 1) • qDer Q q ν (Q.e k) := by
  rw [map_e hS hμ g hgd h1, qDer_e, Finset.sum_range_succ', δ.dpow_zero hμ, smul_add,
    smul_smul, mul_geom_sum, Finset.smul_sum]
  simp only [hν, smul_smul, mul_assoc, Nat.sub_zero, one_mul, sub_smul, one_smul]
  abel

theorem map_sub_self {δ : DividedPowers J} {Q : PDPoly B} {η : DividedPowers (Q.ext J)}
    (hS : Q.IsStd δ η) {q : B} (hμ : q - 1 ∈ J) {ν : ℕ → B}
    (hν : ∀ m, δ.dpow (m + 1) (q - 1) = (q - 1) * ν (m + 1))
    (g : Q.P →+* Q.P) (hgB : g.comp (algebraMap B Q.P) = algebraMap B Q.P)
    (hgd : IsDPMorphism η η g)
    (h1 : g (Q.e 1) = algebraMap B Q.P (q - 1) + algebraMap B Q.P q * Q.e 1) (z : Q.P) :
    g z - z = (q - 1) • qDer Q q ν z := by
  have hsm : ∀ (b : B) (w : Q.P), g (b • w) = b • g w := fun b w ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * g w) (RingHom.congr_fun hgB b)
  let gl : Q.P →ₗ[B] Q.P :=
    { toFun := g, map_add' := map_add g, map_smul' := fun b w ↦ by simpa using hsm b w }
  have key : gl - LinearMap.id = (q - 1) • qDer Q q ν :=
    Q.e.ext fun k ↦ by simpa [gl] using map_e_sub hS hμ hν g hgd h1 k
  simpa [gl] using LinearMap.congr_fun key z

theorem main : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (Q : PDPoly B)
    (η : DividedPowers (Q.ext J)), Q.IsStd δ η → ∀ (p : ℕ), p.Prime → IsNilpotent (p : B) →
    ∀ x : B, (∑ i ∈ Finset.range p, x ^ i) ∈ J → ∀ g : Q.P →+* Q.P,
    g.comp (algebraMap B Q.P) = algebraMap B Q.P → IsDPMorphism η η g →
    g (1 + Q.e 1) = algebraMap B Q.P (x ^ p) * (1 + Q.e 1) →
    Function.Injective (algebraMap B Q.P) ∧
    (∀ r, ∀ z ∈ fil η r, g z = z → ∃ m ∈ fil δ (r + 1),
      algebraMap B Q.P m = algebraMap B Q.P (x ^ p - 1) * z) ∧
    ∀ r, ∀ z ∈ fil η r, ∃ y ∈ fil η (r + 1), g y - y = algebraMap B Q.P (x ^ p - 1) * z := by
  intro B _ J δ Q η hS p hp hpn x hx g hgB hgd hg1
  have hrepr : ∀ b : B, Q.e.repr (algebraMap B Q.P b) 0 = b := fun b ↦ by
    rw [Algebra.algebraMap_eq_smul_one, ← Q.e_zero, map_smul]
    simp
  have hμ : x ^ p - 1 ∈ J := by
    rw [← mul_geom_sum]
    exact J.mul_mem_left _ hx
  obtain ⟨hqn, ν, hν1, hνd, hνf, hνn, hνz⟩ := GlobalTheory.T.cyclotomic_divided_power_expansion δ p hp hpn x hx
  obtain ⟨hfm, hfa, -, hfr⟩ := GlobalTheory.T.divided_power_polynomial_filtration δ Q η hS
  have h1 : g (Q.e 1) = algebraMap B Q.P (x ^ p - 1) + algebraMap B Q.P (x ^ p) * Q.e 1 := by
    have := hg1
    rw [map_add (f := _), map_one, mul_add, mul_one, add_comm (1 : Q.P)] at this
    rw [_root_.map_sub, map_one (algebraMap B Q.P)]
    linear_combination this
  have hg := map_sub_self hS hμ hνd g hgB hgd h1
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.connection_on_divided_power_basis Q.e (fil δ) p (x ^ p) ν (qDer Q (x ^ p) ν) hp.ne_zero hpn
    hqn hfm hfa hν1 hνf hνn hνz (qDer_e Q (x ^ p) ν)
  refine ⟨fun a b hab ↦ by rw [← hrepr a, hab, hrepr], ?_, ?_⟩
  · intro r z hz hgz
    have hD : qDer Q (x ^ p) ν ((x ^ p - 1) • z) = 0 := by
      rw [map_smul, ← hg, hgz, sub_self]
    obtain ⟨c, hc⟩ := hker _ hD
    have hc' : algebraMap B Q.P c = algebraMap B Q.P (x ^ p - 1) * z := by
      rw [← Algebra.smul_def, hc, Q.e_zero, Algebra.algebraMap_eq_smul_one]
    refine ⟨c, ?_, hc'⟩
    have hc0 : c = (x ^ p - 1) * Q.e.repr z 0 := by
      have := hrepr c
      rw [hc', ← Algebra.smul_def, map_smul] at this
      simpa using this.symm
    rw [hc0, add_comm]
    have hz0 : Q.e.repr z 0 ∈ fil δ r := by simpa using (hfr r z).1 hz 0
    exact hfm 1 r (Ideal.mul_mem_mul (le_fil_one δ hμ) hz0)
  · intro r z hz
    obtain ⟨y, hy, hDy⟩ := hsurj r z ((hfr r z).1 hz)
    refine ⟨y, (hfr (r + 1) y).2 hy, ?_⟩
    rw [hg, hDy, Algebra.smul_def]

end GlobalTheory.CompanionTheory.PDAcyc
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

theorem _root_.GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  first | exact @GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | exact GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | (intros; apply GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Frob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def evalMap {π : Representation ℂ (GL (Fin (a + b)) k) V} {σ : Representation ℂ (GL (Fin a) k) W}
    {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    V →ₗ[ℂ] TensorProduct ℂ W W' :=
  φ.toLinearMap ∘ₗ (twKer π (unipRad k (two (stdSum (rfl : a + b = a + b)))) 1).mkQ

theorem evalMap_law {π : Representation ℂ (GL (Fin (a + b)) k) V}
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ))
    (q : parab k (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    evalMap φ (π q w) =
      (deltaHalf k (Two (Fin a) (Fin b)) (leviProj k _ q) : ℂ) •
        extTensor σ ρ ((leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q)) (evalMap φ w) := by
  set xy := (leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q) with hxy
  have hL : leviProj k (two (stdSum (rfl : a + b = a + b))) q = leviTwo k _ _ xy :=
    (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k (two (stdSum (rfl : a + b = a + b))) q
  rw [hL] at hpu ⊢
  have hpu' : (q : GL (Fin (a + b)) k) =
      leviEmb k (two (stdSum (rfl : a + b = a + b))) (leviTwo k _ _ xy) * u := hpu
  have hmk : (Submodule.Quotient.mk (π u w) :
      Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) = Submodule.Quotient.mk w := by
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨u, hu⟩, w, ?_⟩
    simp
  have key : ∀ (M : Levi k (Two (Fin a) (Fin b))) (x : V),
      (Submodule.Quotient.mk (π (leviEmb k (two (stdSum (rfl : a + b = a + b))) M) x) :
        Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) =
        (deltaHalf k (Two (Fin a) (Fin b)) M : ℂ) •
          _root_.GlobalTheory.SmGL.jac (two (stdSum (rfl : a + b = a + b))) π M (Submodule.Quotient.mk x) := by
    intro M x
    rw [_root_.GlobalTheory.SmGL.jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ φ xy
    (Submodule.Quotient.mk w : Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b)))))
  simp only [evalMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
  change _ • φ (jac₂ (stdSum (rfl : a + b = a + b)) π xy (Submodule.Quotient.mk w)) = _
  rw [hint]
  rfl

def frobMap {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    π.IntertwiningMap (prod₂ σ ρ) :=
  { toFun := fun v => ⟨⟨fun x => evalMap φ (π x v), fun q x => by
        show evalMap φ (π (q * x) v) = _
        rw [map_mul, Module.End.mul_apply]
        exact evalMap_law φ q (π x v)⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
        have hh' : π h v = v := hh
        refine Subtype.ext (funext fun x => ?_)
        show evalMap φ (π (x * h) v) = evalMap φ (π x v)
        rw [map_mul, Module.End.mul_apply, hh'])⟩
    map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (v + w)) = evalMap φ (π x v) + evalMap φ (π x w)
      rw [map_add (f := _), map_add (f := _)]))
    map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (c • v)) = c • evalMap φ (π x v)
      rw [map_smul, map_smul]))
    isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (π h v)) = evalMap φ (π (x * h) v)
      rw [map_mul, Module.End.mul_apply])) }

theorem frobMap_one {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) (v : V) :
    (frobMap hs φ v).1.1 1 = φ (Submodule.Quotient.mk v) := by
  show evalMap φ (π 1 v) = _
  rw [map_one]
  rfl

theorem exists_injective_of_jac₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (σ : Representation ℂ (GL (Fin a) k) W)
    (ρ : Representation ℂ (GL (Fin b) k) W'), IsSmooth π → π.IsIrreducible →
    ∀ φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 →
      ∃ ψ : π.IntertwiningMap (prod₂ σ ρ), Function.Injective ψ := by
  intro k _ _ _ _ a b V W W' _ _ _ _ _ _ π σ ρ hs hπ φ hφ
  refine ⟨frobMap hs φ, ?_⟩
  haveI := hπ
  refine (Representation.IsIrreducible.injective_or_eq_zero (frobMap hs φ)).resolve_right fun h0 => hφ ?_
  ext v
  show φ (Submodule.Quotient.mk v) = 0
  rw [← frobMap_one hs φ v, h0]
  rfl

end GlobalTheory.CompanionTheory.Frob
end
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdInj

theorem prod₂_map_injective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (f : σ.IntertwiningMap σ'), Function.Injective f → ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ' ρ), Function.Injective F := by
  intro k _ _ _ _ r t U U' W _ _ _ _ _ _ σ σ' ρ f hf
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapLeft ρ f) (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom),
    GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.ProdInj
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.contracting_unit_abs_pow_bounds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → 0 < nabs k t ∧ nabs k t < 1 ∧ ∀ d : ℕ, ‖((absPow k (d : ℂ) t : ℂˣ) : ℂ)‖ = nabs k t ^ d := by
  first | exact @GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | exact GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero | (intros; apply GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical


theorem _root_.GlobalTheory.T.induced_in_principal_series : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  first | exact @GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | exact GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | (intros; apply GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace <;> assumption)
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.rayRel_antitone_modulus_and_powMod : ∀ (F : Type) [Field F] [NumberField F], (∀ 𝔣 𝔣' I J : Ideal (𝓞 F), 𝔣' ≤ 𝔣 → RayRel F 𝔣' I J → RayRel F 𝔣 I J) ∧ (∀ l n m : ℕ, n ≤ m → powMod F l m ≤ powMod F l n) := by
  first | exact @GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | exact GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti | (intros; apply GlobalTheory.CompanionTheory.RayFacts.rayRel_mono_powMod_anti <;> assumption)
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.mollification_ae_eq_convolution : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | exact GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | (intros; apply GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv <;> assumption)
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.right_translate_derivative_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral | exact GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral | (intros; apply GlobalTheory.CompanionTheory.PresSobA.IntForm.rR_sub_cls_eq_integral <;> assumption)
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.cosieve_pairing_family_compat : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_gen | exact GlobalTheory.CompanionTheory.KunGlue.glue_gen | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_gen <;> assumption)
end
