module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSigmaList
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

noncomputable section
namespace GlobalTheory.UPel.HT.LieLin
open Matrix

theorem ringHom_mapMatrix_algebraMap_scalar {B T : Type} [CommRing B] [CommRing T] (f : B →+* T) {n : ℕ} (x : B) :
    f.mapMatrix (algebraMap B (Matrix (Fin n) (Fin n) B) x) = algebraMap T (Matrix (Fin n) (Fin n) T) (f x) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
  split_ifs <;> simp

theorem list_prod_matrixActionAfterRingHom_sub_apply {O T : Type} [CommRing O] [CommRing T] {n : ℕ} {B : Type} [CommRing B]
    (M : O →+* Matrix (Fin n) (Fin n) B) (f : B →+* T) {a : ℕ} (c : Fin a → O) (τ : Fin a → (O →+* T))
    (v : Fin n → T) :
    (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))).prod v =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).prod *ᵥ v := by
  have h : (List.ofFn fun i => matAct M f (c i) - algebraMap T (Module.End T (Fin n → T)) (τ i (c i))) =
      (List.ofFn fun i => (M (c i)).map f - algebraMap T (Matrix (Fin n) (Fin n) T) (τ i (c i))).map
        (Matrix.toLinAlgEquiv' (R := T) (n := Fin n)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp_apply, map_sub, AlgEquiv.commutes]
    rfl
  rw [h, ← map_list_prod]
  rfl

theorem lieMod_matAct_iff_lieIdeal_le_ker : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (T : Type) [CommRing T] (f : B →+* T),
    LieMod (matAct M f) D.ω (f (βB b.ρ)) (fun i => (f.comp βB).comp (b.t i)) ↔ lieIdeal b βB M ≤ RingHom.ker f := by
  intro p _ D R _ b B _ βB n M T _ f
  set g : R →+* T := f.comp βB with hg
  set τ : Fin D.a → (𝓞 D.F →+* T) := fun i => g.comp (b.t i) with hτ
  set ρ' : T := g b.ρ with hρ'
  set Nh : 𝓞 D.F →+* Matrix (Fin n) (Fin n) T := f.mapMatrix.comp M with hNh
  let Am : T →+* Matrix (Fin n) (Fin n) T := algebraMap T (Matrix (Fin n) (Fin n) T)
  set P : (Fin D.a → 𝓞 D.F) → Matrix (Fin n) (Fin n) T :=
    fun c => (List.ofFn fun i => (M (c i)).map f - Am (τ i (c i))).prod with hP
  set Q : Matrix (Fin n) (Fin n) T := Nh D.ω - Am (g ((D.tr : R) - b.ρ)) with hQ

  have hmap : ∀ c, f.mapMatrix (lieMat b βB M c) = P c * Q := by
    intro c
    rw [lieMat, map_mul, map_list_prod, List.map_ofFn]
    congr 1
    · congr 2; funext i; rw [Function.comp_apply, map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
    · rw [map_sub, ringHom_mapMatrix_algebraMap_scalar]; rfl
  have hdec : ∀ v, (∃ w : Fin D.a → (Fin n → T), (∀ i, w i ∈ eigSub (matAct M f) (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c, P c *ᵥ v = 0 := by
    intro v
    have hcomax : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤ := by
      intro i j hij
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      convert h using 3
      funext x
      simp [hτ]
    rw [GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal (𝓞 D.F) T (Fin n → T) (matAct M f) D.a τ hcomax v]
    simp only [list_prod_matrixActionAfterRingHom_sub_apply, hP]
    rfl

  have hω : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hρ : ρ' * ρ' - (D.tr : T) * ρ' + (D.nm : T) = 0 := by
    have := congrArg g b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    rw [hρ']; linear_combination this
  have hquad : (Nh D.ω - Am ρ') * Q = 0 := by
    have hX : Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) = 0 := by
      have := congrArg Nh hω
      simpa [map_intCast] using this
    have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']
    rw [hQ, hs]
    calc (Nh D.ω - Am ρ') * (Nh D.ω - Am ((D.tr : T) - ρ'))
        = Nh D.ω * Nh D.ω - Am (ρ' + ((D.tr : T) - ρ')) * Nh D.ω + Am (ρ' * ((D.tr : T) - ρ')) := by
          rw [map_add (f := _), map_mul, sub_mul, mul_sub, mul_sub, add_mul, ← Algebra.commutes ((D.tr : T) - ρ') (Nh D.ω)]
          abel
      _ = Nh D.ω * Nh D.ω - Am (D.tr : T) * Nh D.ω + Am (D.nm : T) := by
          congr 2
          · congr 2; ring
          · congr 1; linear_combination -hρ
      _ = 0 := hX
  have hAm : ∀ (x : T) (v : Fin n → T), Am x *ᵥ v = x • v := by
    intro x v
    simp only [Am, Algebra.algebraMap_eq_smul_one]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hact : ∀ v, matAct M f D.ω v = Nh D.ω *ᵥ v := fun v => rfl
  have hs : g ((D.tr : R) - b.ρ) = (D.tr : T) - ρ' := by simp [hρ']

  have hu : IsUnit (ρ' - ((D.tr : T) - ρ')) := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = 4 * D.nm - D.tr ^ 2 := ⟨(4 * D.nm - D.tr ^ 2).toNat,
      Int.toNat_of_nonneg (by have := D.disc_neg; omega)⟩
    have hkp : k.Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out)]
      intro hd
      apply D.disc_p
      have : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.2 hd
      rw [hk] at this
      have h2 : D.tr ^ 2 - 4 * D.nm = -(4 * D.nm - D.tr ^ 2) := by ring
      rw [h2]; exact (dvd_neg).2 this
    have hkT : IsUnit (k : T) := by
      have := (b.unit k hkp).map g
      simpa using this
    have hsq : (ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ')) = -(k : T) := by
      have : ((k : ℤ) : T) = ((4 * D.nm - D.tr ^ 2 : ℤ) : T) := by rw [hk]
      push_cast at this
      rw [this]; linear_combination 4 * hρ
    have : IsUnit ((ρ' - ((D.tr : T) - ρ')) * (ρ' - ((D.tr : T) - ρ'))) := by
      rw [hsq]; exact hkT.neg
    exact isUnit_of_mul_isUnit_left this
  constructor
  · intro hL
    rw [lieIdeal, Ideal.span_le]
    rintro x ⟨c, i, j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have he : f (lieMat b βB M c i j) = ((P c * Q) *ᵥ Pi.single j 1) i := by
      rw [Matrix.mulVec_single_one, ← hmap]
      rfl
    rw [he, ← Matrix.mulVec_mulVec]
    set w := Q *ᵥ Pi.single j 1 with hw
    have hwe : matAct M f D.ω w = ρ' • w := by
      have h0 : ((Nh D.ω - Am ρ') * Q) *ᵥ Pi.single j 1 = 0 := by rw [hquad, Matrix.zero_mulVec]
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hAm, sub_eq_zero] at h0
      rw [hact, ← hw] at *
      exact h0
    obtain ⟨w', hw'⟩ := hL w hwe
    have := (hdec w).1 ⟨w', hw'⟩ c
    rw [this]; rfl
  · intro hI v hv
    apply (hdec v).2
    intro c
    have hz : P c * Q = 0 := by
      ext i j
      have := hI (Ideal.subset_span ⟨c, i, j, rfl⟩)
      rw [RingHom.mem_ker] at this
      rw [← hmap]
      simpa using this
    have hQv : Q *ᵥ v = (ρ' - ((D.tr : T) - ρ')) • v := by
      rw [hQ, Matrix.sub_mulVec, hAm, ← hact, hv, hs]
      change ρ' • v - ((D.tr : T) - ρ') • v = _
      rw [← sub_smul]
    have h1 : (ρ' - ((D.tr : T) - ρ')) • (P c *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, hz, Matrix.zero_mulVec]
    exact (hu.smul_eq_zero).1 h1

end GlobalTheory.UPel.HT.LieLin
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem form_of_classSums {B X W I κ HV HW : Type} [MeasurableSpace B] [MeasurableSpace X] [Fintype I] [Fintype κ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup HV] [InnerProductSpace ℂ HV] [FiniteDimensional ℂ HV]
    [NormedAddCommGroup HW] [InnerProductSpace ℂ HW] [FiniteDimensional ℂ HW]
    (ν : Measure B) (𝓕 : Set B) (μ : Measure X) (𝓖 : Set X) (k : B → X → W → ℂ) (s : I → B) (wt : I → ℂ) (ev : HV → I → W)
    (F : HW → X → ℂ) (N : ℝ) (th : HV →ₗ[ℂ] HW) (Ψ : HW → B → W) (b : OrthonormalBasis κ ℂ W)
    (hV : ∀ x x', inner ℂ x x' = ∑ j, wt j * inner ℂ (ev x j) (ev x' j))
    (hW : ∀ U U', inner ℂ U U' = (N : ℂ) * l2 μ 𝓖 (F U') (F U))
    (hth : ∀ x g, F (th x) g = ∑ j, wt j * k (s j) g (ev x j))
    (hint : ∀ U w h, IntegrableOn (fun g => k h g w * starRingEnd ℂ (F U g)) 𝓖 μ)
    (hΨ : ∀ U h w, inner ℂ (Ψ U h) w = l2 μ 𝓖 (fun g => k h g w) (F U))
    (hex : ∀ U, ∃ a, ∀ j, ev a j = (N : ℂ) • Ψ U (s j)) (U₁ U₂ : HW)
    (hsum : ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν = ∑ j, wt j * inner ℂ (Ψ U₁ (s j)) (Ψ U₂ (s j)))
    (hi : ∀ a, IntegrableOn (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => k h g (b a)) (F U₂))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) := by
  have h1 : ∀ U j, ev (LinearMap.adjoint th U) j = (N : ℂ) • Ψ U (s j) := fun U => by
    obtain ⟨a, ha⟩ := hex U
    have : LinearMap.adjoint th U = a := by
      refine ext_inner_right ℂ fun x => ?_
      rw [LinearMap.adjoint_inner_left, hW, hV, l2_sum_eq_sum_norm_sq_of_orthogonal μ 𝓖 wt (fun j g => k (s j) g (ev x j)) _ _ (hth x) fun j => hint U _ _,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ha, inner_smul_left, Complex.conj_ofReal, hΨ, mul_left_comm]
    rwa [this]
  have e2 : ∑ a, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₁)) (fun h => l2 μ 𝓖 (fun g => k h g (b a)) (F U₂)) =
      ∫ h in 𝓕, inner ℂ (Ψ U₁ h) (Ψ U₂ h) ∂ν := by
    refine (integral_finsetSum _ fun a _ => hi a).symm.trans ?_
    congr 1
    funext h
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hΨ, ← hΨ, inner_conj_symm]
  rw [e2, hsum, hV, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h1, h1, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  ring

theorem inner_law {B W : Type} [Group B] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : B →* Module.End ℂ W)
    (hρ : ∀ h x y, inner ℂ (ρ h x) (ρ h y) = inner ℂ x y) {z : ℂ} (hz : ‖z‖ = 1) (k : B) (a b : W) :
    inner ℂ (z • ρ k a) (z • ρ k b) = inner ℂ a b := by
  rw [inner_smul_left, inner_smul_right, hρ, ← mul_assoc, Complex.conj_mul', hz]
  simp

section Adjoint

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (Datum.WO V W → ℂ)} (hω : Datum.IsWeilDatumO ψ V W χS χT ω)
  (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
  (φ : c.W →ₗ[ℂ] (Datum.WO V W → ℂ)) (hφ : ∀ w, Datum.IsThetaFunO ψ V W (φ w))
  (hinf : ∀ u ∈ GinfC V, ∀ w, ω (u, 1) (φ w) = φ (c.ρ u w))
  (hlev : ∀ κ ∈ Lev.levA V (lev D.sp.cm V.gram β L), ∀ w, ω (κ, 1) (φ w) = (Lev.levChi V β L κ)⁻¹ • φ w)
  {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)} (HW : HMod (MMap M)) {N : ℝ}
  (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y))

include hW in
theorem pet_eq (y y' : HW.H) (v w : M.Vec) :
    l2 μ 𝓖 (HW.e y' w) (HW.e y v) = ipM M μ 𝓖 (HW.e y) (HW.e y') * ∏ τ, ⟪(v τ : M.H τ), (w τ : M.H τ)⟫_ℂ := by
  rw [← (isMultiplicityInner_of_model HW hW y y' v w).2, l2_eq_star]

include hW in
theorem inner_eq_pet (y y' : HW.H) (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) :
    inner ℂ y y' = (N : ℂ) * l2 μ 𝓖 (HW.e y' v) (HW.e y v) := by
  rw [pet_eq HW hW, hW, Finset.prod_eq_one, mul_one]
  intro τ _
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

variable {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕)
  {I : Type} [Fintype I] {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y)
  (HV : HMod (Bridge.Gf V → c.W))
  (hV : HV.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L))
    (Bridge.adInner (Bridge.ratF V) (grpOf V β L) y))
  (v : M.Vec) (hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1) (th : HV.H →ₗ[ℂ] HW.H)
  (hth : ∀ x g, HW.e (th x) v g = ∫ h in 𝓕, Datum.thetaKO ω h g (φ (c.ext (HV.e x) h)) ∂ν)
  (hint : ∀ (U : HW.H) w h, IntegrableOn (fun g => Datum.thetaKO ω h g (φ w) * starRingEnd ℂ (HW.e U v g)) 𝓖 μ)

include hc in
theorem upVec_mem (Ψ : GA D V → c.W) (h2 : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ h,
      Ψ (γ * h * k) = Lev.levChi V β L k • c.ρ k⁻¹ (Ψ h)) :
    (fun u => Ψ (finLift V u)) ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (grpOf V β L) (chrOf V β L) :=
  mem_adForms (finHom V).rangeRestrict (GQ V) c.ρ (finLift V) (finLift_spec V) (fun u => hc.1 _ (finLift_mem V u)) Ψ
      fun γ hγ k hk x => h2 γ hγ k ((mem_grpOf V β L k).1 hk) x


include hω hc hφ hinf hlev hW hν hy hV hv hth hint in
theorem form_eq_sum (U₁ U₂ : HW.H) {κ : Type} [Fintype κ] (b : OrthonormalBasis κ ℂ c.W)
    (hi : ∀ k, IntegrableOn (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v) *
      starRingEnd ℂ (l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v))) 𝓕 ν) :
    inner ℂ (LinearMap.adjoint th U₁) (LinearMap.adjoint th U₂) = (N : ℂ) ^ 2 *
      ∑ k, l2 ν 𝓕 (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₁ v))
        (fun h => l2 μ 𝓖 (fun g => Datum.thetaKO ω h g (φ (b k))) (HW.e U₂ v)) := by
  have h0 := fun U => exists_upVec hω c hc β L φ hφ hinf hlev μ 𝓖 (HW.e U v) (hint U)
  have h1 := fun U => (h0 U).choose_spec.1
  have h2 := fun U => (h0 U).choose_spec.2
  refine form_of_classSums ν 𝓕 μ 𝓖 (fun h g w => Datum.thetaKO ω h g (φ w)) (fun j => finLift V (y j))
    (fun j => ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹) (fun x j => HV.e x (y j))
    (fun U => HW.e U v) N th (fun U => (h0 U).choose) b hV.2.2 (fun U U' => inner_eq_pet HW hW U U' v hv)
    (fun x g => ?_) hint h1 (fun U => ?_) U₁ U₂ ?_ hi
  · exact (hth x g).trans (theta_classSum hω c hc β L φ hφ hinf hlev hν hy (HMod_mem hV x) g)
  · exact (HMod_onto hV (Submodule.smul_mem _ (N : ℂ) (upVec_mem c hc β L _ (h2 U)))).imp fun a ha j => congrFun ha (y j)
  · refine integral_eq_classSum V β L hν hy _ fun γ hγ k hk x => ?_
    exact (congrArg₂ (inner ℂ) (h2 U₁ γ hγ k hk x) (h2 U₂ γ hγ k hk x)).trans
      (inner_law c.ρ hc.2.1 (norm_levChi β L k) _ _ _)

end Adjoint

theorem tsum_eval {Y : Type} (Z kf p : Y → ℂ) (C s : ℂ) (h1 : ∀ y, Z y = C * kf y * starRingEnd ℂ (p y))
    (h2 : HasSum (fun y => kf y * starRingEnd ℂ (p y)) s) : ∑' y, Z y = C * s := by
  simp only [h1, mul_assoc]
  exact (h2.mul_left C).tsum_eq

theorem integral_pi_eval {ι : Type} [Fintype ι] {X : ι → Type} [∀ ρ, MeasurableSpace (X ρ)] (m : ∀ ρ, Measure (X ρ))
    [∀ ρ, SigmaFinite (m ρ)] (a : ∀ ρ, X ρ → ℂ) (Φ : (∀ ρ, X ρ) → ℂ) (c0 z q : ℂ)
    (h : ∀ b, Φ b = c0 * (∏ ρ, a ρ (b ρ)) * 1 * (z * starRingEnd ℂ (q * ∏ ρ, a ρ (b ρ)))) :
    ∫ b, Φ b ∂(Measure.pi m) = c0 * z * starRingEnd ℂ q * ((∏ ρ, ∫ x, ‖a ρ x‖ ^ 2 ∂(m ρ) : ℝ) : ℂ) := by
  have e : ∀ b, Φ b = c0 * z * starRingEnd ℂ q * ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) := fun b => by
    have : ((∏ ρ, ‖a ρ (b ρ)‖ ^ 2 : ℝ) : ℂ) = (∏ ρ, a ρ (b ρ)) * starRingEnd ℂ (∏ ρ, a ρ (b ρ)) := by
      rw [Complex.mul_conj', norm_prod]
      push_cast
      rw [Finset.prod_pow]
    rw [h, this, map_mul]
    ring
  simp only [e]
  rw [integral_const_mul, integral_complex_ofReal, integral_fintype_prod_eq_prod fun ρ x => ‖a ρ x‖ ^ 2]

theorem realMat_mem (i : Fin D.R.m) {Fr : Frames (Wc D i)} (hFr : IsFrames (Wc D i) Fr) (ρ : D.what₂.Tau) (b : Upq (Wc D i) ρ) :
    realMat (Wc D i) Fr ρ b ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ) := by
  refine GlobalTheory.AdelicScalar.conjFrame_mem_UH _ _ _ ((sig_add i ρ).trans (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).symm) _ _ (hFr ρ) ?_ b
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact ((map_ne_zero _).2 (GlobalTheory.DefiniteQuotient.gram_hermND (Wc D i)).2).isUnit

theorem rTr_mul (W : HSp D) (a b : GA D W) (F : GA D W → ℂ) : rTr W (a * b) F = rTr W a (rTr W b F) := by
  funext h
  simp only [rTr, mul_assoc]

theorem coef_translate {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (θ : Datum.InfFam D)
    {J : Set (GA D W)} {χ : GA D W → ℂ} (U₁ U₂ : HW.H) (hU : HW.e U₁ ∈ Mult θ M J χ)
    (g : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (hg : ∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (v : M.Vec) :
    ∃ w : M.Vec, rTr W (realElt θ W g) (HW.e U₁ v) = HW.e U₁ w ∧
      l2 μ 𝓖 (HW.e U₁ w) (HW.e U₂ v) =
        ipM M μ 𝓖 (HW.e U₂) (HW.e U₁) * ∏ τ, ⟪(v τ : M.H τ), M.rep τ (g τ) (v τ : M.H τ)⟫_ℂ :=
  ⟨fun ρ => ⟨_, rep_mem_sm M ρ (g ρ) (hg ρ) _ (v ρ).2⟩,
    (GlobalTheory.RealEquiv.mult_realElt D W S θ M J χ _ hU g hg v _ fun _ => rfl).symm, pet_eq HW hW U₂ U₁ v _⟩

theorem eq_of_value {W : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel W S} {μ : Measure (GA D W)} {𝓖 : Set (GA D W)}
    (HW : HMod (MMap M)) {N : ℝ} (hW : ∀ x y, inner ℂ x y = (N : ℂ) * ipM M μ 𝓖 (HW.e x) (HW.e y)) (U₁ U₂ : HW.H) :
    inner ℂ U₁ U₂ = (N : ℂ) * starRingEnd ℂ (ipM M μ 𝓖 (HW.e U₂) (HW.e U₁)) := by
  rw [← inner_conj_symm, hW, map_mul, Complex.conj_ofReal]

end GlobalTheory.AdelicScalar

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.contDiff_thetaTransform_realLines_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (w + L t) := by
  first | exact @GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | exact GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM | (intros; apply GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM <;> assumption)
end

section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.canonGaugeBiadditive_of_logSum_actionLinear : AddSt → ActSt → BiaddSt := by
  first | exact @GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | exact GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act | (intros; apply GlobalTheory.IsoTriv.GaugeBiadd.biadd_of_add_of_act <;> assumption)
end

section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.columnInclusionIntegral_of_limitSteps : LimActSt → LimPtSt → LimFrameSt → InclSt := by
  first | exact @GlobalTheory.IsoTriv.Incl.inclSt_of_lim | exact GlobalTheory.IsoTriv.Incl.inclSt_of_lim | (intros; apply GlobalTheory.IsoTriv.Incl.inclSt_of_lim <;> assumption)
end

section

open GlobalTheory.IsoTriv

theorem _root_.GlobalTheory.T.frameSeriesExpSum_of_actionLinear_logUnit : ActSt → UnitSt → FrameSt := by
  first | exact @GlobalTheory.IsoTriv.frameSt_of | exact GlobalTheory.IsoTriv.frameSt_of | (intros; apply GlobalTheory.IsoTriv.frameSt_of <;> assumption)
end
