module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle277
public import Formalism.LocalRingCardinality.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle997
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle998
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle783
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle723
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle251
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.BlockNumber

theorem factor_eq_exp {a : ℕ} (nu : DomWeight a) (y : ℕ → ℚ) (b : ℕ) (L : ℝ) (h0 : ∀ l, 0 ≤ nu.w l)
    (hy : ∀ l : Fin a, ((nu.w l : ℤ) : ℚ) = y l) :
    (Real.exp L)⁻¹ ^ GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu * Real.exp 1 * (2 * (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) + 2) ^ (2 * (a * b)) *
      Real.exp (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)) =
    Real.exp (((∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) - ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) * L) +
      (1 + 2 * ((a : ℝ) * b) * Real.log (2 * ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) + 2))) := by
  have hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ) := fun l => by rw [← hy l]; simp
  have hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) := by
    rw [Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]
    have := Int.toNat_of_nonneg (h0 l)
    exact_mod_cast this.symm
  have hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ) := by
    rw [Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]; rfl
  rw [hs, hp]
  set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu
  have hpos : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2)) := by
    conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem sq_le_exp (C A g T : ℕ) (G r L : ℝ) (hG : 1 ≤ G) (hT : 1 ≤ T) (hr : 0 ≤ r) (hg : 1 ≤ g) (hA : g ≤ A) :
    (G ^ (C * A) * ((T : ℝ) * G) ^ (2 * (2 * g)) * Real.sqrt (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp (L / 2)) ^ 2 ≤
      Real.exp (L + ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2)) + 2 * (((C : ℝ) + 4) * A * Real.log (G * T)))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hGT : 1 ≤ G * T := one_le_mul_of_one_le_of_one_le hG hT'
  have hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1 := by positivity
  have h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2) := by positivity
  have e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g := by
    rw [Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]; congr 1; ring
  have e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) := by
    rw [← pow_add]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Real.exp (L / 2) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]
  have b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A)) := by
    rw [mul_comm (C * A) 2]
    exact pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _
  have b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A) := by
    rw [mul_comm (T : ℝ) G]
    exact pow_le_pow_right₀ hGT (by omega)
  have b3 : (3 : ℝ) ≤ 8 ^ g := by
    calc (3 : ℝ) ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have hG0 : 0 ≤ G := by linarith
  calc G ^ (C * A * 2) * ((T : ℝ) * G) ^ (2 * (2 * g) * 2) * (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L
      ≤ (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) * (8 ^ g * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L := by gcongr
    _ = _ := by ring

theorem tmax_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  intro C
  refine ⟨(C : ℝ) + 4, by positivity, ?_⟩
  intro N δ T i ι _ pl nu logOm logTh hi hT h0 hy
  have hm := N.R.two_le_m
  have hk := N.R.m_add_three_le_k
  have ha : 1 ≤ N.R.N i := by unfold Ranks.N; omega
  have hb : 1 ≤ N.R.N (i + 1) := by unfold Ranks.N; omega
  have hf : 1 ≤ N.R.f := by
    have : 0 < N.R.ord := N.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have haN : N.R.N i ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have hbN : N.R.N (i + 1) ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1) := Nat.mul_pos (Nat.mul_pos hf ha) hb
  have hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2 := by
    have h1 : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc N.R.f * N.R.N i * N.R.N (i + 1) = N.R.f * 1 * (N.R.N i * N.R.N (i + 1)) := by ring
      _ ≤ N.R.f * N.R.m ^ 2 * (N.Nm * N.Nm) := by gcongr
      _ = _ := by ring
  have hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)
  have hr : 0 ≤ N.rd := by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity
  have key := sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA
  have hprod := fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax
  rw [← pl.prod_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]
  have e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by ring
  have e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1)) := by ring
  have e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1) := by push_cast; ring
  rw [e1, e2, e3]
  refine (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold kernelBound_sq NumDatum.nuAbs NumDatum.v
  simp only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]
  push_cast
  simp only [mul_assoc]
  ring

end GlobalTheory.BlockNumber
end

section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.PlaceWeights


open Classical in
theorem sum_ind_algHom (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (v : InfinitePlace K) :
    (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)) = 2 := by
  have h1 : (∑ f : K →ₐ[ℚ] ℂ, (if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0))
      = ∑ f : K →+* ℂ, (if InfinitePlace.mk f = v then (1 : ℝ) else 0) :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)).symm
  rw [h1, Finset.sum_boole, InfinitePlace.card_filter_mk_eq, IsTotallyComplex.mult_eq]
  norm_num

theorem finrank_eq_two_mul (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
  rw [← InfinitePlace.sum_mult_eq]
  simp [IsTotallyComplex.mult_eq, mul_comm]


open Classical in
theorem sum_ind_placeUnder (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ)
    (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M) (v : InfinitePlace K) :
    (∑ ρ : M →ₐ[ℚ] ℂ, (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0)) / (Module.finrank ℚ M : ℝ)
      = 1 / (Fintype.card (InfinitePlace K) : ℝ) := by
  let _ : Algebra K M := (σ₀.codRestrict M h).toAlgebra
  have : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq (fun x => by simp)
  have key := (GlobalTheory.EmbeddingMean.tower (K := ℚ) (A := K) (B := M) (C := ℂ)).2
    (fun f => if InfinitePlace.mk (f : K →+* ℂ) = v then (1 : ℝ) else 0)
  rw [sum_ind_algHom, finrank_eq_two_mul K] at key
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · push_cast
    field_simp

theorem exists_weights : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (σ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (h : ∀ k, σ₀ k ∈ M), ∃ wt : InfinitePlace K → (M →ₐ[ℚ] ℂ) → ℝ, (∀ v ρ, 0 ≤ wt v ρ) ∧ (∀ v, ∑ ρ, wt v ρ = 1) ∧ (∀ v ρ, wt v ρ ≠ 0 → placeUnder σ₀ h ρ = v) ∧ ∀ ρ, (∑ v, wt v ρ) / (Fintype.card (InfinitePlace K) : ℝ) = 1 / (Module.finrank ℚ M : ℝ) := by
  classical
  intro K _ _ _ σ₀ M _ h
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hM : (Module.finrank ℚ M : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := M)).ne'
  refine ⟨fun v ρ => (if placeUnder σ₀ h ρ = v then (1 : ℝ) else 0) *
    ((Fintype.card (InfinitePlace K) : ℝ) / (Module.finrank ℚ M : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro v ρ
    refine mul_nonneg ?_ (by positivity)
    split_ifs <;> norm_num
  · intro v
    have key := sum_ind_placeUnder K σ₀ M h v
    rw [← Finset.sum_mul]
    rw [div_eq_div_iff hM hc] at key
    rw [← mul_div_assoc, div_eq_one_iff_eq hM]
    convert key using 1
    ring
  · intro v ρ hw
    by_contra hne
    exact hw (by simp [hne])
  · intro ρ
    rw [← Finset.sum_mul, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    field_simp

end GlobalTheory.PlaceWeights
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder IntermediateField

namespace GlobalTheory.ColNorms.ExField

theorem exists_field_holdsData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  intro D cc dl B cD K _ _ σ₀ R hC hD hM
  obtain ⟨M₁, hM₁, hE, hc⟩ := hD
  obtain ⟨⟨-, h2, h3⟩, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D
    (GlobalTheory.InducedType.induced_type D).1).2 cc dl hC
  choose Mi hMi hcoef using fun i : Fin R.m => hM i.1 i.2
  let M₀ : IntermediateField ℚ ℂ := σ₀.toRatAlgHom.fieldRange
  haveI f0 : FiniteDimensional ℚ M₀ :=
    (AlgEquiv.ofInjectiveField σ₀.toRatAlgHom).toLinearEquiv.finiteDimensional
  let M₂ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g2 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  let M₃ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g3 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  haveI f2 : FiniteDimensional ℚ M₂ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h2).isIntegral
  haveI f3 : FiniteDimensional ℚ M₃ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h3).isIntegral
  haveI f1 : FiniteDimensional ℚ M₁ := inferInstance
  haveI f4 : FiniteDimensional ℚ (⨆ i, Mi i : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let M : IntermediateField ℚ ℂ := (M₀ ⊔ M₁) ⊔ (M₂ ⊔ M₃) ⊔ ⨆ i, Mi i
  have l0 : M₀ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have l1 : M₁ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have l2 : M₂ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  have l3 : M₃ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  have l4 : ∀ i, Mi i ≤ M := fun i => le_sup_of_le_right (le_iSup Mi i)
  refine ⟨M, inferInstance, fun k => l0 ⟨k, rfl⟩, ⟨fun τ x => l1 (hE τ x),
    l2 (IntermediateField.mem_adjoin_simple_self _ _), l3 (IntermediateField.mem_adjoin_simple_self _ _)⟩,
    fun τ => ?_, fun i hi α => l4 ⟨i, hi⟩ (hcoef ⟨i, hi⟩ α)⟩
  obtain ⟨s, hs, -⟩ := hc τ
  exact hs ▸ l1 s.2

end GlobalTheory.ColNorms.ExField
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem logDerivLOne_eq_of_prime_eq (D : D7) (N : NumDatum) (hd : N.d = D.host.d) : N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D := by
  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime), a = b →
      (haveI : Fact a.Prime := ⟨ha⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ)) 1).re) =
      (haveI : Fact b.Prime := ⟨hb⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ)) 1).re) := by
    rintro a b ha hb rfl
    rfl
  exact key _ _ N.hyp.2.1 D.host.hyp.2.1 hd

theorem numbers_of_hostTie : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  intro D N X s Pr h
  have hrd : N.rd = D.host.rdE := h.rd_eq
  obtain ⟨hR, hq, hd, hcc, -, -, hX, -⟩ := h
  have hv : N.v = D.host.v := by
    rw [NumDatum.v, Host.v, hrd]
  have hL := logDerivLOne_eq_of_prime_eq D N hd
  have hfr : Module.finrank ℚ X.E = Module.finrank ℚ D.host.E :=
    (AlgEquiv.ofRingEquiv (f := s.iE) (fun x => by simp) : X.E ≃ₐ[ℚ] D.host.E).toLinearEquiv.finrank_eq
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [hfr, D.host.finrank_E', hR]
  have htower : Module.finrank ℚ X.F * Module.finrank X.F X.E = Module.finrank ℚ X.E :=
    Module.finrank_mul_finrank ℚ X.F X.E
  refine ⟨hrd, hv, hL, ?_, ?_, ?_, hE, ?_, ?_⟩
  · rw [NumDatum.logOm, TaylorLogMetric.logOmVal, hv, hL]
  · rw [TaylorLogMetric.fF, hR]
  · rw [hX.ok.rankE, hE] at htower
    rw [Fields.f, hX.ok.card_Tau]
    omega
  · rw [hrd, Host.rdE, hfr, discr_eq_discr_of_ringEquiv X.E s.iE]
  · rw [hcc]
    refine ⟨top_ne_bot, ?_⟩
    simp

end GlobalTheory.ColNorms
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

theorem _root_.GlobalTheory.T.lintegral_expRho_eq_setLIntegral_unitBallDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Base X) (s : ℝ), ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x0.1 z))) ∂muF X x0.1 = ∫⁻ z in Om X, ENNReal.ofReal (density X x0 z) * ENNReal.ofReal (Real.exp (-(s * rho X z))) := by
  first | exact @GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | exact GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om | (intros; apply GlobalTheory.IntBall.lintegral_exp_muF_eq_setLIntegral_Om <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.CechPic

namespace GlobalTheory.FieldChangeInter

variable {X X' : Scheme.{0}}

def cechIso {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X) {κ : Type} [LinearOrder κ]
    (D : κ → X.Opens) :
    letI := algebraΓOfHom f
    cechLB f M D ≅ cech R (LB.toMod M) ⊤ D :=
  letI := algebraΓOfHom f
  (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
    (M := SecOnR f M (⨅ i ∈ s, D i)) (M₂ := sectionsOn (LB.toMod M) (⊤ ⊓ ⨅ i ∈ s, D i))
    (SecOnR.restrict f M (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, D i) ≤ ⨅ i ∈ s, D i))
    (SecOnR.restrict_bijective f _ (le_inf le_top le_rfl)))
    fun {s t} h x => (SecOnR.restrict_restrict f _ inf_le_right x).trans
      (SecOnR.restrict_restrict f inf_le_right (cechOpen_anti ⊤ D h) x).symm)

theorem nonempty_homology_equiv {R : Type} (O : Type) [CommRing R] [CommRing O]
    [Algebra R O] [Module.Flat R O] (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ) :
    Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
      C).homology n ≃ₗ[O] O ⊗[R] C.homology n) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
  have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology n)
  exact ⟨((C.sc n).mapHomologyIso
    (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩

theorem nonempty_coh_equiv {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {M : LB X} (hM : M.IsLB)
    {κ : Type} [LinearOrder κ] [Finite κ] {D : κ → X.Opens} (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (n : ℕ) :
    letI := algebraΓOfHom f
    Nonempty ((cechLB f M D).homology n ≃ₗ[R] coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  haveI := LB.isQuasicoherent_toMod hM
  exact ⟨((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechIso f M D)).toLinearEquiv ≪≫ₗ
    cechHEquivCoh R hc hD (LB.toMod M) n ≪≫ₗ (cohOn.mapIso R ⊤ n (Twist.unitTwistIso M)).symm⟩

variable {k E : Type} [Field k] [Field E] [Algebra k E] {f : X ⟶ Spec (CommRingCat.of k)}
  {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X}

theorem hdim_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    hdim E (twist (structureModule X') (M.pull π)) n = hdim k (twist (structureModule X) M) n := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  obtain ⟨e₁⟩ := nonempty_coh_equiv f hM hc hD' n
  obtain ⟨e₂⟩ := nonempty_coh_equiv f' (LB.isLB_pull hM π) (D := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := nonempty_homology_equiv E (cechLB f M D) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (cechLBBaseChangeIso hM H hD')).toLinearEquiv
  rw [hdim_def, hdim_def, ← e₁.finrank_eq, ← e₂.finrank_eq]
  exact e₄.finrank_eq.symm.trans (e₃.finrank_eq.trans Module.finrank_baseChange)

theorem interNum_pull [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {ι : Type} [Fintype ι] {L : ι → LB X}
    (hL : ∀ i, (L i).IsLB) :
    letI := algebraΓOfHom f
    letI := algebraΓOfHom f'
    interNum E (structureModule X') (fun i => (L i).pull π) = interNum k (structureModule X) L := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have h : chiPic k (structureModule X) = chiPic E (structureModule X') ∘ pull π := by
    funext c
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    exact finsum_congr fun n => congrArg (fun a : ℕ => (-1 : ℤ) ^ n * a) (hdim_pull H hM n).symm
  rw [interNum_eq_multiDiff k _ hL, h, multiDiff_comap, Function.comp_apply, map_zero,
    interNum_eq_multiDiff E _ fun i ↦ pull_isLB (hL i) π]
  rfl

theorem del_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (S : LinSys k),
    IsProjOver S.str → (S.baseChange E).del = S.del := by
  intro k E _ _ _ S h
  have : IsProper S.str := by
    obtain ⟨N, i, hi, e⟩ := h
    have := isProper_str k N
    rw [← e]
    infer_instance
  exact interNum_pull (ι := Fin S.D) (L := fun _ => S.L) (S.isPullback_baseChange E) fun _ => S.isLB

end GlobalTheory.FieldChangeInter
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (exact GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzTau

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), d.Prime → 4 < d → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ Sz l lam 0 (jT τ) ∧ ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else if l = d then 1 / 2 else 0) ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N x τ) / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro l hl lam d Λ c Ω τ hd h4 hΛ hτ hΩ
  obtain ⟨hst, him⟩ := GlobalTheory.T.imagQuadIntegerLattice_mulStable_I_sqrt d Λ hd.pos hΛ
  refine ⟨GlobalTheory.QFam.pow_twelve_eq_DD Λ c τ hτ Ω hΩ, ?_, ?_⟩
  · refine (GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam).1 1 (jT τ) hl.out.not_dvd_one ?_
    rw [Nat.cast_one, one_mul]
    exact GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ _ hτ hst him
  · intro N _ M x hM hx hx0
    obtain ⟨h1, h2⟩ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ hτ
    rw [add_div, h1, (h2 N x).1, ← add_div]
    have hh := (GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ hτ).1
    refine GlobalTheory.T.denominator_bound_weierstrass_cm_torsion l lam d Λ Ω _ M hd h4 hst hΩ hM ?_ ?_
    · rw [hh, (GlobalTheory.WpFam.TorsMem.main N τ).2.2.1 x]
      exact hx0
    · rw [mul_left_comm, hh]
      exact (GlobalTheory.WpFam.natCast_mul_tors_mem_lattice_iff N τ M x).2 hx

end GlobalTheory.SzTau
end
