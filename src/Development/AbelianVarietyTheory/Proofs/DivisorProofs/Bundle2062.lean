module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle336
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def contr (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) :
    Fin d → E := fun j => ∑ i, X i j * (J *ᵥ fun m => σ (x m)) i

theorem hTens_eq_form (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) = form σ JB (contr σ JA X x) y := by
  unfold GlobalTheory.WeilM.hTens form contr
  simp only [Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hTens_smul_vec (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) E) (JB : Matrix (Fin d) (Fin d) E)
    (X : Matrix (Fin n) (Fin d) E) (c : E) (x : Fin n → E) (y : Fin d → E) :
    GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec (c • x) y) = σ c * GlobalTheory.WeilM.hTens σ JA JB X (Matrix.vecMulVec x y) := by
  unfold GlobalTheory.WeilM.hTens
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem decomp_sum (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin d) E)
    (p f : Fin n → Fin n → E) (h : ∀ k l, form σ J (p k) (f l) = if k = l then 1 else 0) :
    X = ∑ k, Matrix.vecMulVec (p k) (contr σ J X (f k)) := by
  set P : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => p k i with hP
  set Q : Matrix (Fin n) (Fin n) E := Matrix.of fun i k => (J *ᵥ fun m => σ (f k m)) i with hQ
  have h1 : Pᵀ * Q = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← h k l]
    simp [P, Q, form, dotProduct]
  have h2 : Q * Pᵀ = 1 := mul_eq_one_comm.mp h1
  have h3 : P * Qᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  ext i j
  have e : X i j = ((P * Qᵀ) * X) i j := by rw [h3, Matrix.one_mul]
  rw [e, Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, contr, P, Q, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem incM_smul {m k : Type} (c : F) (Z : Matrix m k E) : incM F (c • Z) = algebraMap F (AF F) c • incM F Z := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply]
  rw [Algebra.smul_def c, Algebra.smul_def (algebraMap F (AF F) c), map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).commutes c

theorem inv_mem_O {v : Pl (F := F)} {t : 𝓞 F} (ht : t ∉ v.asIdeal) :
    algebraMap F (Fv F v) ((t : F))⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (t : F) = 1 := by
    have := (v.valuation_eq_one_iff_notMem (K := F)).2 ht
    simpa using this
  have h2 := v.valuedAdicCompletion_eq_valuation' ((t : F)⁻¹)
  have h3 : v.valuation F (t : F)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  exact (h2.trans h3).le

theorem sigma_surj (σ : E →ₐ[F] E) (o : 𝓞 E) : ∃ o' : 𝓞 E, σ (o' : E) = o := by
  obtain ⟨e, he⟩ := (AlgHom.bijective σ).2 (o : E)
  have hi : IsIntegral ℤ e := by
    have h : IsIntegral ℤ (σ e) := he ▸ NumberField.RingOfIntegers.isIntegral_coe o
    exact (isIntegral_algHom_iff (σ.restrictScalars ℤ) σ.injective).1 h
  exact ⟨⟨e, hi⟩, he⟩

theorem lemD (σ : E →ₐ[F] E) (B : Base F E) {n d r s r' s' : ℕ} (X : Spc F E n) (Y : Spc F E d)
    (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s') (v : Pl (F := F))
    (X₀ : Matrix (Fin n) (Fin d) E)
    (hint : ∀ x ∈ X.L, ∀ y ∈ Y.L, algebraMap F (Fv F v)
      (Algebra.trace F E (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y))) ∈ v.adicCompletionIntegers F) :
    GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  have hloc : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧
      IsIntegral ℤ (algebraMap F E (t : F) * GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) := by
    intro x hx y hy
    obtain ⟨t, ht, hti⟩ := GlobalTheory.T.exists_prime_to_place_denominator_unramified_trace F E hun v (-GlobalTheory.WeilM.hTens σ X.J Y.J X₀ (Matrix.vecMulVec x y)) (fun o => by
      obtain ⟨o', ho'⟩ := sigma_surj σ o
      have hx' : (o' : E) • x ∈ X.L := X.L.smul_mem o' hx
      have h := hint _ hx' y hy
      rw [hTens_smul_vec, ho'] at h
      rwa [mul_neg])
    refine ⟨t, ht, ?_⟩
    have h := hti.neg
    rwa [mul_neg, neg_neg] at h
  obtain ⟨f, p, hf, hp, hpf⟩ := GlobalTheory.T.exists_basis_with_dual_basis_in_hermitian_lattice_away_place F E σ B X hX v
  have hw : ∀ k, ∃ t : 𝓞 F, t ∉ v.asIdeal ∧ algebraMap F E (t : F) • contr σ X.J X₀ (f k) ∈ Y.L := by
    intro k
    obtain ⟨s0, hs0, hsf⟩ := hf k
    refine GlobalTheory.T.skewSelfDual_lattice_localised_at_place F E σ B Y hY v _ fun y hy => ?_
    obtain ⟨t, ht, hti⟩ := hloc _ hsf y hy
    refine ⟨t * s0, fun h => (v.isPrime.mem_or_mem h).elim ht hs0, ?_⟩
    rw [← hTens_eq_form]
    rw [hTens_smul_vec, AlgHom.commutes] at hti
    convert hti using 1
    rw [show ((t * s0 : 𝓞 F) : F) = (t : F) * (s0 : F) from rfl, map_mul]
    ring
  choose tw htw hwY using hw
  choose tp htp hpX using hp
  have hdec := decomp_sum σ X.J X₀ p f hpf
  rw [hdec]
  have hsum : incM F (∑ k, Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) =
      ∑ k, incM F (Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k))) := by
    ext i j

    simp [incM, Matrix.sum_apply, map_sum]
  rw [hsum, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
  have hc0 : (tp k * tw k : 𝓞 F) ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim (htp k) (htw k)
  have hne : (tp k * tw k : 𝓞 F) ≠ 0 := fun h => hc0 (h ▸ zero_mem _)
  have hcF : ((tp k * tw k : 𝓞 F) : F) ≠ 0 := by
    intro h0
    exact hne (by exact_mod_cast h0)
  have hcE : algebraMap F E ((tp k * tw k : 𝓞 F) : F) ≠ 0 := (map_ne_zero _).2 hcF
  have hvm : Matrix.vecMulVec (p k) (contr σ X.J X₀ (f k)) = ((tp k * tw k : 𝓞 F) : F)⁻¹ •
      Matrix.vecMulVec (algebraMap F E (tp k : F) • p k) (algebraMap F E (tw k : F) • contr σ X.J X₀ (f k)) := by
    ext i j
    rw [show ((tp k * tw k : 𝓞 F) : F) = (tp k : F) * (tw k : F) from rfl] at hcE ⊢
    rw [map_mul] at hcE
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [Algebra.smul_def ((tp k : F) * (tw k : F))⁻¹, map_inv₀, map_mul]
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ hcE]
    ring
  refine ⟨GlobalTheory.EmbChart.atPlace v (algebraMap F (Fv F v) ((tp k * tw k : 𝓞 F) : F)⁻¹), (fun u hu => by
      rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]), ?_, _,
    hpX k, _, hwY k, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]
    exact inv_mem_O hc0
  · rw [hvm, incM_smul, smul_smul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul, AlgHom.commutes]

theorem latAtV_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV G.V' G.W v ↔ ∀ γ ∈ latAtV G.V' G.W v,
        B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin z hz
  have hB := hT.base
  have hV' := hT.geo.hV'
  have hW := hT.geo.hW
  have h1v : evFin F v (1 : AF F) ∈ v.adicCompletionIntegers F := by rw [map_one]; exact one_mem _
  constructor
  · intro hzΓ γ hγ
    have h := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v z hzΓ γ hγ
    simpa using h
  · intro hc
    obtain ⟨X₀, hX₀⟩ := GlobalTheory.T.matrix_adelic_decomposition_at_finite_place F E G.V' G.W hV'.lat hW.lat v z hz
    have hc₀ : ∀ γ ∈ latAtV G.V' G.W v, B.ψ (symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J)
        (GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) γ) = 1 := by
      intro γ hγ
      have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B G.V' G.W _ _ _ _ hB hV' hW v (-1) 1 h1v _ hX₀ γ hγ
      have hm : inclR (F := F) (AF F) (((-1 : 𝓞 E)) : E) = -1 := by simp
      rw [hm, one_mul] at h1
      have e : GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ = z + -(z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) := by abel
      rw [e, GlobalTheory.LatVacArith.symp_add_left, GlobalTheory.LatVacArith.symp_neg_left, AddChar.map_add_eq_mul,
        AddChar.map_neg_eq_inv, hc γ hγ, h1, inv_one, one_mul]
    have hint := GlobalTheory.T.trace_hermitianTensor_integral_of_char_trivial F E σ B.ψ G.V' G.W v (hB.inert v w hin).2.2 X₀ hc₀
    have hmem := lemD σ B G.V' G.W hB.unram hV' hW v X₀ hint
    have e : z = (z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀) + GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ := by abel
    rw [e]
    exact add_mem hX₀ hmem

end GlobalTheory.InertDual
end
end

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.ThetaSchurF

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem half_add_half (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y = symplOF σ JS JT ξ₀ x y := by
  simp only [symplOHF, ← add_mul, ← map_add (f := _)]
  norm_num

theorem symplOF_add_left (x x' y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (x + x') y = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x' y := by
  simp only [symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOF_add_right (x y y' : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ x (y + y') = symplOF σ JS JT ξ₀ x y + symplOF σ JS JT ξ₀ x y' := by
  simp only [symplOF, hOF, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplOF_zero_right (x : WOF F E nS nT) : symplOF σ JS JT ξ₀ x 0 = 0 := by
  simp [symplOF, hOF]

theorem continuous_symplOF_left (y : WOF F E nS nT) : Continuous fun x => symplOF σ JS JT ξ₀ x y := by
  have h := GlobalTheory.HeisThetaF.continuous_symplOHF_left (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) y
  have e : (fun x => symplOF σ JS JT ξ₀ x y) = fun x => symplOHF σ JS JT ξ₀ x y + symplOHF σ JS JT ξ₀ x y :=
    funext fun x => (half_add_half x y).symm
  rw [e]
  exact h.add h

theorem mul_star_psi (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF F) : ψ a * star (ψ a) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hψ a]
  simp

theorem heis_rat (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT)
    (x : WOF F E nS nT) : heisOF σ JS JT ξ₀ ψ γ f x = ψ (symplOF σ JS JT ξ₀ x γ) * f x := by
  obtain ⟨γ, rfl⟩ := hγ
  have hs : symplOHF σ JS JT ξ₀ (ratWF γ) x = -symplOHF σ JS JT ξ₀ x (ratWF γ) := by
    simp only [symplOHF]
    rw [hskew, mul_neg]
  show ψ (symplOHF σ JS JT ξ₀ x (ratWF γ)) * f (x + ratWF γ) = ψ (symplOF σ JS JT ξ₀ x (ratWF γ)) * f x
  rw [add_comm x, hf.quasi, hs, neg_neg, ← mul_assoc, ← AddChar.map_add_eq_mul, half_add_half]

theorem prod_periodic (hψ : ∀ a, ‖ψ a‖ = 1) {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f)
    (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') {γ : WOF F E nS nT} (hγ : γ ∈ ratLF F E nS nT) (x : WOF F E nS nT) :
    f (γ + x) * star (f' (γ + x)) = f x * star (f' x) := by
  obtain ⟨γ, rfl⟩ := hγ
  show f (ratWF γ + x) * star (f' (ratWF γ + x)) = _
  rw [hf.quasi, hf'.quasi, star_mul']
  linear_combination (f x * star (f' x)) * mul_star_psi hψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x))

theorem scalar_eq (hψ : ∀ a, ‖ψ a‖ = 1) (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ)
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hn : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    (f f' : WOF F E nS nT → ℂ) (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f') :
    ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ (g : WOF F E nS nT → ℂ), g ∈ GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C :=
    fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => by
      have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖g (γ + w)‖ = ‖g w‖ := by
        rintro _ ⟨γ, rfl⟩ w
        exact (congrArg norm (hg.quasi γ w)).trans (by rw [norm_mul, hψ, one_mul])
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.cont.continuousOn
      refine ⟨C, fun w => ?_⟩
      obtain ⟨γ, hγ, h⟩ := hKc w
      rw [← hp γ hγ w]
      exact hC _ h
  exact GlobalTheory.Mem.LiftPolar.integral_mul_star_eq (μ.restrict 𝓕) (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (fun g (hg : IsThetaFunOF σ JS JT ξ₀ ψ g) => hg.cont.measurable) hb M hM hn f f' hf hf'

theorem prod_eq (hψ : IsCharAF F ψ)
    (hskew : ∀ x y : WOF F E nS nT, symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y)
    (hann : ∀ x : WOF F E nS nT, (∀ γ ∈ ratLF F E nS nT, ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT)
    (hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (heisOF σ JS JT ξ₀ ψ w f))
    (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (hM : ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f → IsThetaFunOF σ JS JT ξ₀ ψ (M f))
    (hc : ∀ w f, IsThetaFunOF σ JS JT ξ₀ ψ f → M (heisOF σ JS JT ξ₀ ψ w f) = heisOF σ JS JT ξ₀ ψ w (M f))
    (hn : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ ψ f →
        ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ)
    {f f' : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ ψ f) (hf' : IsThetaFunOF σ JS JT ξ₀ ψ f')
    (x : WOF F E nS nT) : M f x * star (M f' x) = f x * star (f' x) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, 𝓕, hμ, h𝓕, -⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hint : ∀ g g', IsThetaFunOF σ JS JT ξ₀ ψ g → IsThetaFunOF σ JS JT ξ₀ ψ g' →
      Integrable (fun x => g x * star (g' x)) (μ.restrict 𝓕) := fun g g' hg hg' => by
    have hcont : Continuous fun x => g x * star (g' x) := hg.cont.mul hg'.cont.star
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← prod_periodic hψ.2.1 hg hg' hγ w]
    exact hC _ h
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WOF F E nS nT) (ratLF F E nS nT) K hK hKc
    (ratLF F E nS nT) (fun γ x => ψ (symplOF σ JS JT ξ₀ x γ))
    (fun γ => hψ.1.comp (continuous_symplOF_left _))
    (fun γ x y => by simp only [symplOF_add_left, AddChar.map_add_eq_mul])
    (fun γ γ' x => by simp only [AddSubgroup.coe_add, symplOF_add_right, AddChar.map_add_eq_mul])
    (fun x => by simp only [AddSubgroup.coe_zero, symplOF_zero_right, AddChar.map_zero_eq_one])
    (fun γ x => hψ.2.1 _)
    (fun x => by
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩)
    μ 𝓕 hμ h𝓕 (fun x => M f x * star (M f' x) - f x * star (f' x))
    (((hM f hf).cont.mul (hM f' hf').cont.star).sub (hf.cont.mul hf'.cont.star))
    (fun γ hγ x => by
      rw [prod_periodic hψ.2.1 hf hf' hγ, prod_periodic hψ.2.1 (hM f hf) (hM f' hf') hγ])
    (fun γ => by
      have e : (fun x => ψ (symplOF σ JS JT ξ₀ x γ) * (M f x * star (M f' x) - f x * star (f' x))) = fun x =>
          M (heisOF σ JS JT ξ₀ ψ γ f) x * star (M f' x) - heisOF σ JS JT ξ₀ ψ γ f x * star (f' x) := by
        funext x
        rw [hc _ f hf, heis_rat hskew hf γ.2, heis_rat hskew (hM f hf) γ.2]
        ring
      rw [e, integral_sub (hint _ _ (hM _ (hth _ f hf)) (hM f' hf')) (hint _ _ (hth _ f hf) hf'),
        scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 M hM (hn μ 𝓕 hμ h𝓕) _ _ (hth _ f hf) hf', sub_self])
  exact sub_eq_zero.1 (congrFun key x)

end Lemmas

theorem schur : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := GlobalTheory.T.rational_points_self_annihilator_symplectic_standardChar F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs : star (M f₀ y) ≠ 0 := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]

end GlobalTheory.ThetaSchurF

end
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_standardPositiveDefinite_hermitianSpace_rank : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  first | exact @GlobalTheory.StdDefSpace.exists_std_definite | exact GlobalTheory.StdDefSpace.exists_std_definite | (intros; apply GlobalTheory.StdDefSpace.exists_std_definite <;> assumption)
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_volumeOne_measure_definite_openCompact : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))), IsDefiniteSpace V → IsOpenCompactLevel V K →
  ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), Links.IsMeasDef V K μ 𝓕 := by
  first | exact @GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | exact GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact | (intros; apply GlobalTheory.DefiniteLevelMeasure.exists_isMeasDef_openCompact <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.testFunctions_transport_localLatticeIsometries : ∀ (D : D7) (V V' : HSp D), V'.rank = V.rank → ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) → (∀ v g, j v g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), ∃ (T' : TypeDataG V') (U' : AuxiliaryPlaceHermitianSpace V'), (NoFixed T → NoFixed T') ∧ ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) ff, IsTestFin T U μf ff → IsTestFin T' U' (fun v => (μf v).map (j v)) (transfer j ff) := by
  first | exact @GlobalTheory.LatTransport.isTestFin_transport | exact GlobalTheory.LatTransport.isTestFin_transport | (intros; apply GlobalTheory.LatTransport.isTestFin_transport <;> assumption)
end
