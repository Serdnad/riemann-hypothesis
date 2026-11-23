module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuples
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometriesFixingSubspaceLeQuasiReflectionClosure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuasiReflectionStabilizesLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexTupleLatticeHermitianLatticeUniformizer
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeLocalStructureDiscriminan
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle035
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SameTrace

open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

theorem hf_zero_r (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

theorem exists_smul_mem [IsNonarchimedeanLocalField F] {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsLat L Λ) (x : Fin n → E) : ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.CommonDenominator.main
  | exact _root_.GlobalTheory.CommonDenominator.main
  | (apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominator.main ..)

noncomputable def shear {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := v + ∑ j, hf L Hm v (b j) • d j
  map_add' v w := by simp only [hf_add_l, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [hf_smul_l, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul]
  invFun v := v - ∑ j, hf L Hm v (b j) • d j
  left_inv v := by simp [hf_add_l, hf_sum_l, hf_smul_l, hdb]
  right_inv v := by simp [hf_sub_l, hf_sum_l, hf_smul_l, hdb]

theorem shear_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : shear L Hm b d hdb v = v + ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_symm_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : (shear L Hm b d hdb).symm v = v - ∑ j, hf L Hm v (b j) • d j := rfl

theorem shear_mem_isomG {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by
  intro v w
  have hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j) := by
    intro k

    rw [← hf_cj L h, hv, map_sum]
    simp only [map_mul, hf_cj L h]
  simp only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [hw]
  simp only [hv v, Finset.mul_sum]
  have key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k))
      + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k
  linear_combination key

end

theorem exists_isometry_of_same_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ La Lb, IsSD L Hm La → IsSD L Hm Lb → ∀ (m : ℕ) (e : Fin m → Fin n → E), LinearIndependent E e → (∀ i j, hf L Hm (e i) (e j) = 0) → (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), x ∈ La ↔ x ∈ Lb) → ∃ g ∈ isomG L Hm, (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), g x = x) ∧ g • La = Lb := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH La Lb hLa hLb m e he hee hab
  obtain ⟨-, hA, -, b, c, hb, hc, hbc⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH La hLa m e he
  obtain ⟨-, hB, -, -⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH Lb hLb m e he
  set X := Submodule.span E (Set.range e) with hX
  have hcj := hf_cj L hH.1

  have hXp : ∀ x ∈ X, x ∈ perp L Hm X := by
    have h1 : ∀ i, e i ∈ perp L Hm X := by
      intro i y hy
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      simp [hf_sum_r, hf_smul_r, hee]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 h1)
  have hbm : ∀ j, b j ∈ La ∧ b j ∈ X := fun j => by
    have : b j ∈ La ⊓ X.restrictScalars L.O := by
      rw [hb]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hbLb : ∀ j, b j ∈ Lb := fun j => (hab _ (hXp _ (hbm j).2)).1 (hbm j).1
  have hcb : ∀ i j, hf L Hm (c i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [← hcj, hbc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hperp : ∀ v, (∀ j, hf L Hm v (b j) = 0) → v ∈ perp L Hm X := by
    intro v hv x hx
    obtain ⟨t, ht, htx⟩ := exists_smul_mem L hLa.1 x
    have h1 : algebraMap F E t • x ∈ Submodule.span L.O (Set.range b) := by
      rw [← hb]; exact ⟨htx, X.smul_mem _ hx⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : hf L Hm v (algebraMap F E t • x) = 0 := by
      rw [← ha]
      simp [hf_sum_r, Subring.smul_def, hf_smul_r, hv]
    rw [hf_smul_r, AlgEquiv.commutes] at h2
    have ht' : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
    exact ((IsUnit.mk0 _ ht').map (algebraMap F E)).mul_right_eq_zero.1 h2
  have hint : ∀ {Λ}, IsSD L Hm Λ → ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O :=
    fun hΛ x hx y hy => (hΛ.2 y).2 hy x hx

  have hc' : ∀ j, ∃ a ∈ Lb, c j - a ∈ X := fun j =>
    (hB (c j)).1 fun x hx hxp => hint hLa x ((hab x hxp).2 hx) _ (hc j)
  choose c' hc'b hc'X using hc'
  obtain ⟨ω, hω, ε, hε, hωε⟩ := exists_sub_cj_mul_eq_one L
  have hε' : (L.cj ω - ω) * L.cj ε = 1 := by simpa [L.cj_cj] using congrArg L.cj hωε
  have hcε : L.cj ε = -ε := by linear_combination (-ε) * hε' - (L.cj ε) * hωε
  obtain ⟨τ, hτO, hτ⟩ : ∃ τ ∈ L.O, τ + L.cj τ = 1 :=
    ⟨ω * ε, L.O.mul_mem hω hε, by rw [map_mul, hcε]; linear_combination hωε⟩
  let d₀ : Fin m → Fin n → E := fun j => c' j - c j
  have hd₀ : ∀ j, d₀ j ∈ X := fun j => by
    have := X.neg_mem (hc'X j)
    rwa [neg_sub] at this
  let H : Fin m → Fin m → E := fun j k => hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)
  have hHO : ∀ j k, H j k ∈ L.O := fun j k => by
    have h0 : hf L Hm (d₀ j) (d₀ k) = 0 := hXp _ (hd₀ j) _ (hd₀ k)
    have h1 : H j k = hf L Hm (c' j) (c' k) - hf L Hm (c j) (c k) := by
      simp only [H, d₀, hf_sub_l, hf_sub_r] at h0 ⊢
      linear_combination -h0
    rw [h1]
    exact L.O.sub_mem (hint hLb _ (hc'b j) _ (hc'b k)) (hint hLa _ (hc j) _ (hc k))
  have hHc : ∀ j k, L.cj (H k j) = H j k := fun j k => by
    simp only [H, map_add (f := _), hcj]; ring
  let d : Fin m → Fin n → E := fun j => d₀ j - ∑ l, (τ * H j l) • b l
  have hd : ∀ j, d j ∈ X := fun j =>
    X.sub_mem (hd₀ j) (X.sum_mem fun l _ => X.smul_mem _ (hbm l).2)
  have hcdb : ∀ j, c j + d j ∈ Lb := fun j => by
    have h1 : c j + d j = c' j - ∑ l, (τ * H j l) • b l := by
      simp only [d, d₀]; abel
    rw [h1]
    exact Lb.sub_mem (hc'b j) (Lb.sum_mem fun l _ =>
      Lb.smul_mem ⟨_, L.O.mul_mem hτO (hHO j l)⟩ (hbLb l))
  have hdb : ∀ i j, hf L Hm (d i) (b j) = 0 := fun i j => hXp _ (hd i) _ (hbm j).2
  have hdd : ∀ i j, hf L Hm (d i) (d j) = 0 := fun i j => hXp _ (hd i) _ (hd j)
  have hv0 : ∀ v, v - ∑ j, hf L Hm v (b j) • c j ∈ perp L Hm X := fun v =>
    hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hcb]
  have hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k) := fun v k => by
    have h1 := hv0 v _ (hd k)
    simp only [hf_sub_l, hf_sum_l, hf_smul_l] at h1
    exact sub_eq_zero.1 h1
  have hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0 := fun j k => by
    have h1 : hf L Hm (c j) (d k) = hf L Hm (c j) (d₀ k) - L.cj τ * H j k := by
      simp [d, hf_sub_r, hf_sum_r, hf_smul_r, hcb, hHc]
    have h2 : hf L Hm (d j) (c k) = hf L Hm (d₀ j) (c k) - τ * H j k := by
      simp [d, hf_sub_l, hf_sum_l, hf_smul_l, hbc]
    have h3 : H j k = hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k) := rfl
    rw [h1, h2]
    linear_combination -h3 - H j k * hτ
  refine ⟨shear L Hm b d hdb, shear_mem_isomG L hH.1 b c d hdb hdd hv hcd, fun x hx => ?_, ?_⟩
  · have h1 : ∀ j, hf L Hm x (b j) = 0 := fun j => hx _ (hbm j).2
    simp [shear_apply, h1]
  · apply le_antisymm
    · rintro _ ⟨v, hva, rfl⟩
      show shear L Hm b d hdb v ∈ Lb
      have hβ : ∀ j, hf L Hm v (b j) ∈ L.O := fun j => hint hLa _ hva _ (hbm j).1
      have h1 : shear L Hm b d hdb v = (v - ∑ j, hf L Hm v (b j) • c j)
          + ∑ j, hf L Hm v (b j) • (c j + d j) := by
        simp only [shear_apply, smul_add, Finset.sum_add_distrib]; abel
      rw [h1]
      refine Lb.add_mem ((hab _ (hv0 v)).1 (La.sub_mem hva (La.sum_mem fun j _ =>
        La.smul_mem ⟨_, hβ j⟩ (hc j)))) (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j))
    · intro w hw
      refine ⟨(shear L Hm b d hdb).symm w, ?_, (shear L Hm b d hdb).apply_symm_apply w⟩
      have hβ : ∀ j, hf L Hm w (b j) ∈ L.O := fun j => hint hLb _ hw _ (hbLb j)
      have h1 : (shear L Hm b d hdb).symm w = (w - ∑ j, hf L Hm w (b j) • (c j + d j))
          + ∑ j, hf L Hm w (b j) • c j := by
        simp only [shear_symm_apply, smul_add, Finset.sum_add_distrib]; abel
      have h2 : w - ∑ j, hf L Hm w (b j) • (c j + d j) ∈ perp L Hm X :=
        hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hf_add_l, hcb, hdb]
      show (shear L Hm b d hdb).symm w ∈ La
      rw [h1]
      refine La.add_mem ((hab _ h2).2 (Lb.sub_mem hw (Lb.sum_mem fun j _ =>
        Lb.smul_mem ⟨_, hβ j⟩ (hcdb j)))) (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j))

end GlobalTheory.HL.SameTrace
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), ∃ V0 : ℝ≥0∞, ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = V0 * ENNReal.ofReal (invVol K0 (MulAction.stabilizer G x)) := by
  first | exact @GlobalTheory.HL.mass_orbit_eq | exact GlobalTheory.HL.mass_orbit_eq | (intros; apply GlobalTheory.HL.mass_orbit_eq <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | exact GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | (intros; apply GlobalTheory.HL.SelfDual.exists_orthonormal_same_span <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

theorem ringEquiv_mem_one (e : E ≃+* E) {x : E} (hx : x ∈ (1 : Submodule (𝓞 E) E)) :
    e x ∈ (1 : Submodule (𝓞 E) E) := by
  rw [Submodule.mem_one] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  have hy : IsIntegral ℤ (e (algebraMap (𝓞 E) E y)) :=
    (RingOfIntegers.isIntegral_coe y).map (e : E →+* E).toIntAlgHom
  exact ⟨⟨_, hy⟩, rfl⟩

theorem ringEquiv_mem_dual (e : E ≃+* E) {x : E}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    e x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))] at hx ⊢
  intro a ha
  have ha' : e.symm a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at ha ⊢
    exact ringEquiv_mem_one e.symm ha
  have h := hx _ ha'
  let f : E ≃ₐ[ℚ] E := AlgEquiv.ofRingEquiv (f := e) (fun q => map_ratCast e q)
  have key : Algebra.traceForm ℚ E (e x) a = Algebra.traceForm ℚ E x (e.symm a) := by
    simp only [Algebra.traceForm_apply]
    have : e x * a = f (x * e.symm a) := by
      rw [map_mul]
      show e x * a = e x * e (e.symm a)
      rw [RingEquiv.apply_symm_apply]
    rw [this, Algebra.trace_eq_of_algEquiv]
  rw [key]; exact h

theorem ringEquiv_mem_pow (e : E ≃+* E) (M : Submodule (𝓞 E) E) (hM : ∀ x ∈ M, e x ∈ M) :
    ∀ (j : ℕ) (x : E), x ∈ M ^ j → e x ∈ M ^ j := by
  intro j
  induction j with
  | zero => intro x hx; rw [pow_zero] at hx ⊢; exact ringEquiv_mem_one e hx
  | succ j ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]; exact Submodule.mul_mem_mul (ih m hm) (hM n hn)
    · rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem ringEquiv_mem_dInv (e : E ≃+* E) (j : ℕ) (x : E) (hx : x ∈ dInv E j) : e x ∈ dInv E j := by
  have hd : ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ =
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  rw [dInv, hd, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow] at hx ⊢
  exact ringEquiv_mem_pow e _ (fun y hy => ringEquiv_mem_dual e hy) j x hx

theorem conj_mem_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (j : ℕ) (x : E), x ∈ dInv E j → σ x ∈ dInv E j := by
  intro F E _ _ _ _ _ σ _ j x hx
  have hb : Function.Bijective ((σ : E →+* E).toRatAlgHom) := AlgHom.bijective _
  exact ringEquiv_mem_dInv (RingEquiv.ofBijective (σ : E →+* E) hb) j x hx

end GlobalTheory.SnMass.VolN
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_isometry_near_identity_close_tuples : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N : ℕ, ∃ N' : ℕ, ∀ x y : Fin m → Fin n → E, (∀ a, x a ∈ Λ) → gramT L Hm x = Γ → gramT L Hm y = Γ → (∀ a, ∃ w ∈ Λ, y a - x a = algebraMap F E ((ϖ : F) ^ N') • w) → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = y a := by
  first | exact @GlobalTheory.HL.CloseTuples.exists_isometry_close | exact GlobalTheory.HL.CloseTuples.exists_isometry_close | (intros; apply GlobalTheory.HL.CloseTuples.exists_isometry_close <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.isometriesFixingSubspace_le_quasiReflection_closure : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → fixG L Hm (Submodule.span E (Set.range x)) ≤ Subgroup.closure {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g} := by
  first | exact @GlobalTheory.HL.QReflGen.fixG_le_closure | exact GlobalTheory.HL.QReflGen.fixG_le_closure | (intros; apply GlobalTheory.HL.QReflGen.fixG_le_closure <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_lattice_and_inverting_automorphism_of_quasi_reflection : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ a ∈ perp L Hm (Submodule.span E (Set.range x)), ∀ g, IsQRefl L Hm a g → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ ∃ α : ((Fin n → E) ≃ₗ[E] (Fin n → E)) ≃* ((Fin n → E) ≃ₗ[E] (Fin n → E)), (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ).map α.toMonoidHom = fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ ∧ α g = g⁻¹ := by
  first | exact @GlobalTheory.QRefl.qrefl_inverted | exact GlobalTheory.QRefl.qrefl_inverted | (intros; apply GlobalTheory.QRefl.qrefl_inverted <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.relIndex_tupleLattice_hermitianLattice_uniformizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ m j : ℕ, ((tupLat L Λs m).map (DistribSMul.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (tupLat L Λs m) = resQ ϖ ^ (2 * n * m * j) ∧ ((hermLat L m).map (DistribSMul.toAddMonoidHom _ (algebraMap F E ((ϖ : F) ^ j)))).relIndex (hermLat L m) = resQ ϖ ^ (m ^ 2 * j) := by
  first | exact @GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat | exact GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat | (intros; apply GlobalTheory.HL.LatCard.relIndex_tupLat_hermLat <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.witt_extension_totally_definite_hermitian : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  first | exact @GlobalTheory.Mass.Witt.witt_definite | exact GlobalTheory.Mass.Witt.witt_definite | (intros; apply GlobalTheory.Mass.Witt.witt_definite <;> assumption)
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.MaxLatLam

theorem factor_bounds {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    0 < (q ^ n - (-1) ^ n) / (q + 1) ∧ (q ^ n - (-1) ^ n) / (q + 1) ≤ (q ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : q ≤ q ^ n := le_self_pow₀ (by linarith) (by omega)
  have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ℝ n
  have h3 : (q ^ 2) ^ ((n : ℝ) / 2) = q ^ n := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast q n]
    congr 1
    push_cast
    ring
  refine ⟨div_pos (by rcases h2 with e | e <;> rw [e] <;> linarith) (by linarith), ?_⟩
  rw [h3, div_le_iff₀ (by linarith)]
  rcases h2 with e | e <;> rw [e] <;> nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → 1 ≤ Module.finrank K V → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → 0 < lamMax h M ∧ lamMax h M ≤ (discN h M : ℝ) ^ ((Module.finrank K V : ℝ) / 2) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hnd hn M hM
  obtain ⟨hfin, hd, -, hP⟩ := GlobalTheory.MaxLatStruct.main K V h hK hs hnd M hM
  rw [hd, lamMax, finprod_mem_eq_finite_toFinset_prod _ hfin, finprod_mem_eq_finite_toFinset_prod _ hfin]
  have hq : ∀ P ∈ hfin.toFinset, (2 : ℝ) ≤ (qIn P : ℝ) := fun P hp => by
    exact_mod_cast (hP P (hfin.mem_toFinset.1 hp)).2.1
  refine ⟨Finset.prod_pos fun P hp => (factor_bounds (hq P hp) hn).1, ?_⟩
  rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun P _ => Nat.cast_nonneg _)]
  refine Finset.prod_le_prod₀ (fun P hp => (factor_bounds (hq P hp) hn).1.le) fun P hp => ?_
  rw [(hP P (hfin.mem_toFinset.1 hp)).2.2.1, Nat.cast_pow]
  exact (factor_bounds (hq P hp) hn).2

end GlobalTheory.MaxLatLam
end
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.maximalHermitianLattice_local_structure_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsMaxLat h M → (badP h M).Finite ∧ discN h M = ∏ᶠ P ∈ badP h M, Ideal.absNorm P ∧ Nonempty ((↥(dual h M) ⧸ M.comap (dual h M).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ᶠ P ∈ badP h M, P)) ∧ ∀ P ∈ badP h M, conjIdeal (K := K) P = P ∧ 2 ≤ qIn P ∧ Ideal.absNorm P = qIn P ^ 2 ∧ ∃ x ∈ M, (∃ a : 𝓞 K, (a : K) = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧ ∀ y ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, y - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by
  first | exact @GlobalTheory.MaxLatStruct.main | exact GlobalTheory.MaxLatStruct.main | (intros; apply GlobalTheory.MaxLatStruct.main <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective c.dat ∧ (∀ g ∈ P.UW0, ∀ d d', LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d') ∧ (∀ d d', LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ (∀ d g, g ∈ LocNG.Datum.Stab d ↔ c.grp g ∈ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧ ∀ d0 d, LocNG.Datum.wt d0 d = invVol (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  first | exact @GlobalTheory.HL.CoordDatum.transport | exact GlobalTheory.HL.CoordDatum.transport | (intros; apply GlobalTheory.HL.CoordDatum.transport <;> assumption)
end
