module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.Bundle002
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle009
import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GreenRegularCharacters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory Polynomial Matrix GlobalTheory.GLq

namespace UpperTheory.Zero.LLC

private theorem scalar_comm {g n : ℕ} [Fact g.Prime] (c : (ZMod g)ˣ) (x : Gn g n) :
    GeneralLinearGroup.scalar (Fin n) c * x = x * GeneralLinearGroup.scalar (Fin n) c := by
  ext i j
  simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, mul_comm]

private theorem schur_scalar {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G) [Simple τ] (s : G)
    (hs : ∀ x : G, s * x = x * s) : ∃ l : ℂ, ∀ v : τ, τ.ρ s v = l • v := by
  let F : τ ⟶ τ := ⟨FGModuleCat.ofHom (τ.ρ s), fun x => by
    ext v
    change τ.ρ s (τ.ρ x v) = τ.ρ x (τ.ρ s v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hs]⟩
  obtain ⟨l, hl⟩ := endomorphism_simple_eq_smul_id ℂ F
  refine ⟨l, fun v => ?_⟩
  have : F.hom.hom.hom v = l • v := by rw [← hl]; rfl
  exact this

private theorem charpoly_lmul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] {n : ℕ}
    (b : Module.Basis (Fin n) F K) (x : K) (hd : (minpoly F x).natDegree = n) :
    (Algebra.leftMulMatrix b x).charpoly = minpoly F x := by
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h0 : aeval x (Algebra.leftMulMatrix b x).charpoly = 0 := by
    apply Algebra.leftMulMatrix_injective b
    rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) (Matrix.charpoly_monic _)
    (minpoly.dvd F x h0) (by rw [Matrix.charpoly_natDegree_eq_dim, hd, Fintype.card_fin])

private theorem natDegree_smul {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (c : Fˣ) (x : K) : (minpoly F (algebraMap F K c * x)).natDegree = (minpoly F x).natDegree := by
  have hE : IntermediateField.adjoin F {algebraMap F K c * x} = IntermediateField.adjoin F {x} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.mem_adjoin_simple_self F x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h : algebraMap F K (c⁻¹ : Fˣ) * (algebraMap F K c * x) = x := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      have hm := mul_mem (IntermediateField.algebraMap_mem
        (IntermediateField.adjoin F {algebraMap F K c * x}) ((c⁻¹ : Fˣ) : F))
        (IntermediateField.mem_adjoin_simple_self F (algebraMap F K c * x))
      rwa [h] at hm
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral _),
    ← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x), hE]

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.nameCentral :
    UpperTheory.Zero.LLC.NameCentral := by
  intro g _ n hn K _ _ hK τ θ hcusp hreg hnames c v
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (hK ▸ hn)
  haveI : Simple τ := DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hcusp.2.1
  obtain ⟨l, hl⟩ := UpperTheory.Zero.LLC.schur_scalar τ (GeneralLinearGroup.scalar (Fin n) c)
    (UpperTheory.Zero.LLC.scalar_comm c)
  obtain ⟨⟨z, hzdeg, hS⟩, -⟩ := UpperTheory.Zero.LLC.pin g n hn K hK θ hreg
  let b : Module.Basis (Fin n) (ZMod g) K := Module.finBasisOfFinrankEq _ _ hK
  let L : Kˣ →* Gn g n := Units.map (Algebra.leftMulMatrix b).toMonoidHom
  let cK : Kˣ := Units.map (algebraMap (ZMod g) K).toMonoidHom c
  let z' : Kˣ := cK * z
  have hz' : (z' : K) = algebraMap (ZMod g) K c * z := rfl
  have hy : ((L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b z := rfl
  have hsy : ((GeneralLinearGroup.scalar (Fin n) c * L z : Gn g n) : Matrix (Fin n) (Fin n) (ZMod g))
      = Algebra.leftMulMatrix b z' := by
    rw [Units.val_mul, hy, hz', map_mul, AlgHom.commutes]
    ext i j
    simp [GeneralLinearGroup.scalar, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
  have hchar : ∀ (w : Kˣ), (minpoly (ZMod g) (w : K)).natDegree = n → ∀ M : Gn g n,
      (M : Matrix (Fin n) (Fin n) (ZMod g)) = Algebra.leftMulMatrix b w →
      τ.character M = (-1) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (w ^ g ^ j) : ℂ) := by
    intro w hw M hM
    have hc : (M : Matrix (Fin n) (Fin n) (ZMod g)).charpoly = minpoly (ZMod g) (w : K) := by
      rw [hM]
      exact UpperTheory.Zero.LLC.charpoly_lmul b w hw
    refine hnames M ?_ w ?_
    · rw [hc]
      exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
    · rw [hc]
      exact minpoly.aeval _ _
  have hz'deg : (minpoly (ZMod g) (z' : K)).natDegree = n := by
    rw [hz', UpperTheory.Zero.LLC.natDegree_smul]
    exact hzdeg
  have h1 := hchar z hzdeg (L z) hy
  have h2 := hchar z' hz'deg _ hsy
  have hρ : τ.ρ (GeneralLinearGroup.scalar (Fin n) c) = l • (1 : Module.End ℂ τ.V) :=
    LinearMap.ext fun w => by rw [hl]; simp
  have h3 : τ.character (GeneralLinearGroup.scalar (Fin n) c * L z) = l * τ.character (L z) := by
    simp only [FDRep.character, map_mul, hρ, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  have hcpow : ∀ j : ℕ, cK ^ g ^ j = cK := by
    intro j
    ext
    simp [cK, Units.val_pow_eq_pow_val, ← map_pow, ZMod.pow_card_pow]
  have hsum : ∑ j ∈ Finset.range n, (θ (z' ^ g ^ j) : ℂ)
      = (θ cK : ℂ) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [z', mul_pow, hcpow, map_mul, Units.val_mul]
  rw [h1, h2, hsum] at h3
  have hne : ((-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, (θ (z ^ g ^ j) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hS
  have hl' : l = (θ cK : ℂ) := by
    apply mul_right_cancel₀ hne
    linear_combination -h3
  rw [hl, hl']
end

section

noncomputable section

open Polynomial GlobalTheory.GLq

namespace UpperTheory.Zero.LLC

private theorem exists_elt {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (z : Kˣ) (hz : (minpoly (ZMod g) (z : K)).natDegree = n) :
    ∃ y : Gn g n, Irreducible (y : Mt g n).charpoly ∧ aeval (z : K) (y : Mt g n).charpoly = 0 := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hn)
  have hint : IsIntegral (ZMod g) (z : K) := IsIntegral.of_finite (ZMod g) (z : K)
  have hdim : (Algebra.adjoin.powerBasis hint).dim = n := hz
  have hmin : minpoly (ZMod g) (Algebra.adjoin.powerBasis hint).gen = minpoly (ZMod g) (z : K) := by
    have h := minpoly.algHom_eq (Algebra.adjoin (ZMod g) {(z : K)}).val Subtype.val_injective
      (Algebra.adjoin.powerBasis hint).gen
    exact h.symm
  have hchar : (Matrix.reindex (finCongr hdim) (finCongr hdim)
      (Algebra.leftMulMatrix (Algebra.adjoin.powerBasis hint).basis
        (Algebra.adjoin.powerBasis hint).gen)).charpoly = minpoly (ZMod g) (z : K) := by
    rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, hmin]
  have hdet : IsUnit (Matrix.reindex (finCongr hdim) (finCongr hdim)
      (Algebra.leftMulMatrix (Algebra.adjoin.powerBasis hint).basis
        (Algebra.adjoin.powerBasis hint).gen)).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_eq_sign_charpoly_coeff, hchar]
    refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
    exact minpoly.coeff_zero_ne_zero hint z.ne_zero
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hchar]
    exact minpoly.irreducible hint
  · rw [IsUnit.unit_spec, hchar]
    exact minpoly.aeval _ _

private theorem pow_period {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) : θ ^ g ^ n = θ := by
  haveI : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hn)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [@Module.card_eq_pow_finrank (ZMod g) K _ _ _ _ _, ZMod.card, hK]
  ext z
  rw [MonoidHom.pow_apply, ← map_pow]
  congr 2
  ext
  rw [Units.val_pow_eq_pow_val, ← hc, FiniteField.pow_card]

private theorem pow_add_mul {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m k : ℕ) : θ ^ g ^ (m + n * k) = θ ^ g ^ m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + n * (k + 1) = (m + n * k) + n by ring, pow_add, pow_mul, pow_period hn hK, ih]

private theorem pow_mod {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m : ℕ) : θ ^ g ^ (m % n) = θ ^ g ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  exact (pow_add_mul hn hK θ _ _).symm

private theorem regular_pow {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n) {K : Type} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) {θ : Kˣ →* ℂˣ} (hθ : GlobalTheory.Published.IsRegularChar g n θ) (j : ℕ) :
    GlobalTheory.Published.IsRegularChar g n (θ ^ g ^ j) := by
  intro a b ha hb hab
  apply hθ a b ha hb
  have e1 : ∀ c, θ ^ g ^ c = ((θ ^ g ^ j) ^ g ^ c) ^ g ^ (n * j - j) := by
    intro c
    rw [← pow_mul, ← pow_mul, ← pow_add_mul hn hK θ c j]
    congr 1
    simp only [← pow_add]
    congr 1
    have hj : j ≤ n * j := Nat.le_mul_of_pos_left j hn
    generalize n * j = t at hj ⊢
    omega
  rw [e1 a, e1 b, hab]

theorem nameLaws :
    UpperTheory.Zero.LLC.NameLaws := by
  intro g _ n hn K _ _ hK
  obtain ⟨τF, hτ1, hτ2, hτ3⟩ := PositivityTheory.Stage1.PM.greenRegularCharacters g n hn K hK
  have hnames : ∀ θ : Kˣ →* ℂˣ, GlobalTheory.Published.IsRegularChar g n θ →
      ∀ τ : FDRep ℂ (Gn g n), τ.character = τF θ → Names g n θ τ := by
    intro θ hθ τ hτ y hy z hz
    rw [hτ]
    exact (hτ1 θ hθ).2.2 y hy z hz
  have huniq : ∀ (τ : FDRep ℂ (Gn g n)) (θ θ' : Kˣ →* ℂˣ), GlobalTheory.Published.IsRegularChar g n θ →
      GlobalTheory.Published.IsRegularChar g n θ' → Names g n θ τ → Names g n θ' τ → ∃ j < n, θ' = θ ^ g ^ j := by
    intro τ θ θ' hθ hθ' h1 h2
    refine (UpperTheory.Zero.LLC.pin g n hn K hK θ hθ).2 θ' hθ' fun z hz => ?_
    obtain ⟨y, hy, hyz⟩ := exists_elt hn hK z hz
    have e := (h1 y hy z hyz).symm.trans (h2 y hy z hyz)
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) e
  have hchar : ∀ (τ : FDRep ℂ (Gn g n)) (θ : Kˣ →* ℂˣ), GlobalTheory.GLq.IsCusp τ.character →
      GlobalTheory.Published.IsRegularChar g n θ → Names g n θ τ → τ.character = τF θ := by
    intro τ θ hc hθ hN
    obtain ⟨θ₁, hθ₁, h1⟩ := hτ3 _ hc
    obtain ⟨i, hi, hi'⟩ := huniq τ θ θ₁ hθ hθ₁ hN (hnames θ₁ hθ₁ τ h1)
    rw [h1]
    exact ((hτ2 θ θ₁ hθ hθ₁).mpr ⟨i, hi, hi'⟩).symm
  refine ⟨fun τ hc => ?_, huniq, fun τ τ' θ j hc hc' hθ hN hN' => ?_, fun K' _ _ e τ θ' => ?_⟩
  · obtain ⟨θ, hθ, h⟩ := hτ3 _ hc
    exact ⟨θ, hθ, hnames θ hθ τ h⟩
  · rw [hchar τ' _ hc' (regular_pow hn hK hθ j) hN', hchar τ θ hc hθ hN, ← pow_mod hn hK θ j]
    exact ((hτ2 θ _ hθ (regular_pow hn hK hθ (j % n))).mpr ⟨j % n, Nat.mod_lt _ hn, rfl⟩).symm
  · have hf : ∀ x : ZMod g, e (algebraMap (ZMod g) K x) = algebraMap (ZMod g) K' x := fun x =>
      RingHom.congr_fun
        (RingHom.ext_zmod (e.toRingHom.comp (algebraMap (ZMod g) K)) (algebraMap (ZMod g) K')) x
    let eA : K ≃ₐ[ZMod g] K' := AlgEquiv.ofRingEquiv hf
    refine ⟨fun hN y hy z hz => ?_, fun hreg a b ha hb hab => hreg a b ha hb ?_⟩
    · have hz' : aeval ((Units.map (e.toRingHom : K →* K') z : K'ˣ) : K') (y : Mt g n).charpoly = 0 := by
        have h := Polynomial.aeval_algHom_apply eA.toAlgHom (z : K) (y : Mt g n).charpoly
        rw [hz, map_zero] at h
        exact h
      rw [hN y hy _ hz']
      simp [map_pow]
    · ext z
      obtain ⟨w, rfl⟩ : ∃ w, Units.map (e.toRingHom : K →* K') w = z :=
        ⟨Units.map (e.symm.toRingHom : K' →* K) z, by ext; simp⟩
      have h := congrArg (fun χ : Kˣ →* ℂˣ => χ w) hab
      simp only [MonoidHom.pow_apply, MonoidHom.comp_apply] at h ⊢
      exact congrArg (fun u : ℂˣ => (u : ℂ)) h

end UpperTheory.Zero.LLC

end
end
