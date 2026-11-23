module

public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.DownSlotProposition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
public import Lemmata.PowerMembership.PowMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

theorem pi_isUnit {ι : Type} {R : ι → Type} [∀ i, Monoid (R i)] (f : ∀ i, R i)
    (h : ∀ i, IsUnit (f i)) : IsUnit f :=
  ⟨⟨f, fun i => ((h i).unit⁻¹ : (R i)ˣ), funext fun i => (h i).mul_val_inv,
    funext fun i => (h i).val_inv_mul⟩, rfl⟩

section Gam

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem gam_unit (π' : LetA O n) (E : ZMod n → Polynomial O) {s' : ℕ} (hs' : 1 ≤ s')
    (w2 : (LetA O n)ˣ) (hw2 : W.γA W.gam π' - π' = (w2 : LetA O n) * π' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π')
    (w0 : (LetA O n)ˣ) (hw0 : π' = (w0 : LetA O n) * letπ ^ s') :
    ∃ u : LetA O n, IsUnit u ∧ W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = u * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
  have key : ∀ i, ∃ G : PowerSeries O, (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
      Formalism.MainNotions.DeltaInvariantLattices.Eat E π' i + (W.γA W.gam π' - π') i * G := by
    intro i
    have hi : (W.γA W.gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) i =
        Polynomial.aeval ((W.γA W.gam π') i) (E i) := by
      show W.γ₀ W.gam (Polynomial.aeval (π' i) (E i)) = _
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    obtain ⟨G, hG⟩ := Polynomial.sub_dvd_eval_sub ((W.γA W.gam π') i) (π' i)
      ((E i).map (algebraMap O (PowerSeries O)))
    refine ⟨G, ?_⟩
    rw [hi, Polynomial.aeval_def, ← Polynomial.eval_map, Pi.sub_apply, ← hG]
    show _ = Polynomial.aeval (π' i) (E i) + _
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    ring
  choose G hG using key
  refine ⟨1 + (w2 : LetA O n) * π' * G, ?_, ?_⟩
  · refine pi_isUnit _ fun i => ?_
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h0 : PowerSeries.constantCoeff (π' i) = 0 := by
      rw [hw0]
      show PowerSeries.constantCoeff ((w0 : LetA O n) i * PowerSeries.X ^ s') = 0
      rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
    show IsUnit (PowerSeries.constantCoeff (1 + (w2 : LetA O n) i * π' i * G i))
    rw [map_add (f := _), map_one, map_mul, map_mul, h0, mul_zero, zero_mul, add_zero]
    exact isUnit_one
  · funext i
    rw [Pi.mul_apply, hG i, hw2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply]
    ring

theorem u_mem_AΔ {Eπ u : LetA O n} (hEΔ : Eπ ∈ W.AΔ) (hnz : ∀ a : LetA O n, a * Eπ = 0 → a = 0)
    (hu : W.γA W.gam Eπ = u * Eπ) : u ∈ W.AΔ := by
  intro δ hδ
  have h1 : W.γA δ (u * Eπ) = u * Eπ := by rw [← hu, γA_comm, hEΔ δ hδ]
  rw [map_mul, hEΔ δ hδ] at h1
  exact sub_eq_zero.1 (hnz _ (by rw [sub_mul, h1, sub_self]))

theorem inv_mem_AΔ {u u' : LetA O n} (hu : u ∈ W.AΔ) (huu : u' * u = 1) : u' ∈ W.AΔ := by
  intro δ hδ
  have h2 : W.γA δ u' * u = 1 := by rw [← hu δ hδ, ← map_mul, huu, map_one]
  calc W.γA δ u' = W.γA δ u' * (u * u') := by rw [mul_comm u u', huu, mul_one]
    _ = (W.γA δ u' * u) * u' := by ring
    _ = u' := by rw [h2, one_mul]

theorem q0_ne_two_and_ne_q_and_ne_d (hp : ((PD.p : ℕ) : O) ≠ 0) : W.q₀ ≠ 0 := by
  intro h
  have h1 := W.q₀_def
  rw [h, mul_zero] at h1
  have h2 := congrArg (PowerSeries.coeff 1) h1
  have e : (1 + PowerSeries.X : PowerSeries O) ^ PD.p =
      (((Polynomial.X + 1) ^ PD.p : Polynomial O) : PowerSeries O) := by
    push_cast
    ring
  rw [map_zero, map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_X_add_one_pow,
    Nat.choose_one_right, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero] at h2
  exact hp h2.symm

theorem Eπ_nzd [IsDomain O] {Eπ : LetA O n} {w : LetA O n} (hQ : W.q = w * Eπ) (hq0 : W.q₀ ≠ 0) :
    ∀ a : LetA O n, a * Eπ = 0 → a = 0 := by
  intro a ha
  funext i
  have h := congrFun ha i
  have hE : Eπ i ≠ 0 := fun h0 => by
    have := congrFun hQ i
    change W.q₀ = w i * Eπ i at this
    rw [h0, mul_zero] at this
    exact hq0 this
  exact (mul_eq_zero.1 h).resolve_right hE

end Gam

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Gen

theorem aeval_mem_of_stable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (f : Module.End R M) (hf : ∀ v ∈ S, f v ∈ S) (P : Polynomial R) {v : M}
    (hv : v ∈ S) : Polynomial.aeval f P v ∈ S := by
  first | exact Bl.PowerMembership.goal1 .. | (apply Bl.PowerMembership.goal1 <;> assumption) | (intros; apply Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> assumption) | (intros; apply @Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> first | assumption | infer_instance) | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v hv | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› | exact @Bl.PowerMembership.goal1 R M | exact @Bl.PowerMembership.goal1 R

theorem aeval_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : Module.End R M)
    (P : Polynomial R) (v : M) : Polynomial.aeval f P (f v) = f (Polynomial.aeval f P v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add (f := _)]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply, ← pow_succ, pow_succ',
      Module.End.mul_apply]

theorem ps_coeff_cancel {LL : Type*} [Field LL] (p g : PowerSeries LL)
    (hp : PowerSeries.constantCoeff p ≠ 0) (N : ℕ) (h : ∀ i < N, PowerSeries.coeff i (p * g) = 0) :
    ∀ i < N, PowerSeries.coeff i g = 0 := by
  intro i hi
  have e : g = p⁻¹ * (p * g) := by
    rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [h q.2 (by omega), mul_zero]

end Gen

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

theorem tensor_eq_sum {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) :
    z = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
  calc z = (TensorProduct.equivFinsuppOfBasisRight bL).symm (TensorProduct.equivFinsuppOfBasisRight bL z) := by
        simp
    _ = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
        rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]

theorem coord_γLA {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (γLA W T π' c z) i =
      W.γE W.gamK (TensorProduct.equivFinsuppOfBasisRight bL z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hx, hy, map_add (f := _), Finsupp.add_apply, map_add (f := _)]
  | tmul e l =>
    rw [ModelFPf.γLA_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact ((W.γE W.gamK).toLinearMap.map_smul _ _).symm

theorem coord_sub {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z z' : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (z - z') i =
      TensorProduct.equivFinsuppOfBasisRight bL z i - TensorProduct.equivFinsuppOfBasisRight bL z' i := by
  rw [map_sub, Finsupp.sub_apply]

variable {W T π' c}

theorem valAt_zero (ζ : LL) (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x) : valAt W T c ζ 0 = 0 := by
  have h := hvsmul 0 0 (Submodule.zero_mem _)
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

theorem valAt_sum (ζ : LL)
    (hvadd : ∀ x y, x ∈ NcS W T (c - 1) → y ∈ NcS W T (c - 1) →
      valAt W T c ζ (x + y) = valAt W T c ζ x + valAt W T c ζ y)
    (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x)
    {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T) (hy : ∀ i, y i ∈ NcS W T (c - 1)) :
    valAt W T c ζ (∑ i ∈ s, co i • y i) = ∑ i ∈ s, algebraMap O LL (co i) • valAt W T c ζ (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, valAt_zero ζ hvsmul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hvadd _ _ (Submodule.smul_mem _ _ (hy a)) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)),
      hvsmul _ _ (hy a), ih]

theorem mkL_sum {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T)
    (hy : ∀ i, y i ∈ NcS W T (c - 1)) (h : ∑ i ∈ s, co i • y i ∈ NcS W T (c - 1)) :
    mkL W T π' c (∑ i ∈ s, co i • y i) h = ∑ i ∈ s, co i • mkL W T π' c (y i) (hy i) := by
  have e : (⟨∑ i ∈ s, co i • y i, h⟩ : ↥(NcS W T (c - 1))) = ∑ i ∈ s, co i • ⟨y i, hy i⟩ := by
    ext
    simp
  unfold mkL

  rw [e, show Submodule.Quotient.mk (∑ i ∈ s, co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) =
    ∑ i ∈ s, Submodule.Quotient.mk (p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype)
      (co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) from map_sum (Submodule.mkQ _) _ _]
  simp only [Submodule.Quotient.mk_smul]

end Loc

section NL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable {W} {T : LocLat G Qp LL O} {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' : ℕ}
  {c : ZMod n}

theorem piNL_le (hπΔ : π' ∈ W.AΔ)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) :
    piNL W T Pt π' Eπ h' c 1 ≤ NL W T Pt π' Eπ h' c := by
  rintro _ ⟨y, hy, rfl⟩
  rw [pow_one]
  exact hA π' hπΔ y hy

theorem piNL_γ (hγ : ∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c)
    {uπ : LetA O n} (huπ : uπ ∈ W.AΔ) (hγπ : W.γA W.gamK π' = π' * uπ) {x : LA W T π' c}
    (hx : x ∈ piNL W T Pt π' Eπ h' c 1) : γLA W T π' c x ∈ piNL W T Pt π' Eπ h' c 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨smulLA W T π' c uπ (γLA W T π' c y), hA uπ huπ _ (hγ y hy), ?_⟩
  rw [pow_one, ModelFPf.γLA_smulLA, ModelFPf.smulLA_smulLA, hγπ]

end NL

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end
