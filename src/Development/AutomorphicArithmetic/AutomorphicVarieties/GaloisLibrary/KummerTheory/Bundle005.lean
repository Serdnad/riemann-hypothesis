module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod
public import ReciprocityTheory.Hypotheses.GalCohDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement
public import Mathlib.FieldTheory.Finite.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

open KStar.TotallyRealRoots in
private theorem eg_pow_mem {l : ℕ} [Fact l.Prime] {a : ℕ} (ha : 1 ≤ a) {u : ℤ_[l]ˣ} (hu : u ∈ princ l a) :
    u ^ l ∈ princ l (a + 1) := by
  rw [mem_princ] at hu ⊢
  obtain ⟨c, hc⟩ := hu
  obtain ⟨f, hf⟩ := sq_dvd_add_pow_sub_sub ((l : ℤ_[l]) ^ a * c) 1 l
  have hw : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ a * c := by rw [← hc]; ring
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  refine ⟨c + (l : ℤ_[l]) ^ m * c ^ 2 * f, ?_⟩
  rw [Units.val_pow_eq_pow_val, hw]
  simp only [one_pow, one_mul] at hf
  linear_combination hf

open KStar.TotallyRealRoots in
private theorem eg_exists_not_mem {l : ℕ} [Fact l.Prime] {u : ℤ_[l]ˣ} (hu : u ≠ 1) :
    ∃ a, u ∉ princ l a := by
  by_contra h
  push Not at h
  apply hu
  have hb : IsClosed ((⊥ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  have := mem_of_isClosed hb (x := u) fun b => ⟨1, Subgroup.one_mem _, by
    rw [map_one]; exact (MonoidHom.mem_ker.1 (h b)).symm⟩
  exact Subgroup.mem_bot.1 this

theorem UpperTheory.V.Kum.existsGen :
    ∀ (l : ℕ) [Fact l.Prime] (V : Subgroup ℤ_[l]ˣ), IsClosed (V : Set ℤ_[l]ˣ) → (l ≠ 2 ∨ V ≤ KStar.TotallyRealRoots.princ l 2) → ∃ γ ∈ V, V ≤ (Subgroup.zpowers γ).topologicalClosure := by
  classical
  intro l _ V _ hl
  have hp : l.Prime := Fact.out
  obtain ⟨⟨_, g, hg, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := V.map (KStar.TotallyRealRoots.red l))
  have key : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g →
      V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ (Subgroup.zpowers γ).topologicalClosure →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h v hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨_, Subgroup.mem_map_of_mem _ hv⟩)
    have hk' : KStar.TotallyRealRoots.red l g ^ k = KStar.TotallyRealRoots.red l v := congrArg Subtype.val hk
    have h1 : v * (γ ^ k)⁻¹ ∈ V ⊓ KStar.TotallyRealRoots.princ l 1 := by
      refine Subgroup.mem_inf.2 ⟨V.mul_mem hv (V.inv_mem (V.zpow_mem hγ k)), ?_⟩
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, e, hk',
        mul_inv_cancel]
    have h2 : γ ^ k ∈ (Subgroup.zpowers γ).topologicalClosure :=
      Subgroup.le_topologicalClosure _ (Subgroup.zpow_mem_zpowers γ k)
    simpa using Subgroup.mul_mem _ (h h1) h2
  by_cases hW : V ⊓ KStar.TotallyRealRoots.princ l 1 = ⊥
  · exact ⟨g, hg, key g hg rfl (by rw [hW]; exact bot_le)⟩
  have hex : ∃ b, ¬ V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l b := by
    obtain ⟨⟨w, hw⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hW
    obtain ⟨b, hb⟩ := eg_exists_not_mem (u := w) (fun h => hw1 (Subtype.ext h))
    exact ⟨b, fun h => hb (h hw)⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → V ⊓ KStar.TotallyRealRoots.princ l 1 ≤ KStar.TotallyRealRoots.princ l m :=
    fun m hm => not_not.1 (Nat.find_min hex hm)
  have h1 : 1 < Nat.find hex := by
    by_contra h
    exact hspec (inf_le_right.trans (KStar.TotallyRealRoots.princ_anti (by omega)))
  have h2 : l = 2 → 2 < Nat.find hex := by
    intro h2
    by_contra h
    exact hspec (inf_le_left.trans ((hl.resolve_left (not_not.2 h2)).trans (KStar.TotallyRealRoots.princ_anti (by omega))))
  obtain ⟨a, ha⟩ : ∃ a, Nat.find hex = a + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [ha] at hspec hmin h1 h2
  have hle := hmin a (Nat.lt_succ_self a)
  obtain ⟨u, hu, hua⟩ := SetLike.not_le_iff_exists.1 hspec
  have fin : ∀ γ ∈ V, KStar.TotallyRealRoots.red l γ = KStar.TotallyRealRoots.red l g → γ ^ (l - 1) ∉ KStar.TotallyRealRoots.princ l (a + 1) →
      V ≤ (Subgroup.zpowers γ).topologicalClosure := by
    intro γ hγ e h
    refine key γ hγ e (hle.trans ?_)
    have hm : γ ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l a := by
      refine hle (Subgroup.mem_inf.2 ⟨V.pow_mem hγ _, ?_⟩)
      rw [KStar.TotallyRealRoots.princ_one_eq_ker, MonoidHom.mem_ker, map_pow, ZMod.units_pow_card_sub_one_eq_one]
    refine KStar.TotallyRealRoots.princ_le_of_isClosed (u := γ ^ (l - 1)) (by omega) (fun h => by have := h2 h; omega)
      (Subgroup.isClosed_topologicalClosure _)
      (Subgroup.le_topologicalClosure _ (Subgroup.npow_mem_zpowers γ _)) ?_
    exact emultiplicity_eq_coe.2 ⟨KStar.TotallyRealRoots.mem_princ.1 hm, fun h' => h (KStar.TotallyRealRoots.mem_princ.2 h')⟩
  by_cases hga : g ^ (l - 1) ∈ KStar.TotallyRealRoots.princ l (a + 1)
  · refine ⟨g * u, V.mul_mem hg hu.1, fin _ (V.mul_mem hg hu.1) ?_ ?_⟩
    · have : u ∈ (KStar.TotallyRealRoots.red l).ker := by
        rw [← KStar.TotallyRealRoots.princ_one_eq_ker]
        exact (Subgroup.mem_inf.1 hu).2
      rw [map_mul, MonoidHom.mem_ker.1 this, mul_one]
    · intro h
      rw [mul_pow] at h
      have h3 := (mul_mem_cancel_left hga).1 h
      have h4 := eg_pow_mem (by omega) (hle hu)
      have h5 : u ^ l = u ^ (l - 1) * u := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      rw [h5] at h4
      exact hua ((mul_mem_cancel_left h3).1 h4)
  · exact ⟨g, hg, fin g hg rfl hga⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.cobOfGen :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (γ : Γ),
    Continuous χ → ContAction ρ → (∀ g, χ g = 1 → ∀ m, ρ g m = m) → (∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure) → (Function.Surjective fun m => ρ γ m - m) →
    ∀ z ∈ Z1 ρ, (∀ g, χ g = 1 → z g = 0) → z ∈ B1 ρ := by
  intro l _ Γ _ _ _ _ χ R M _ _ _ _ _ ρ γ hχ hρ hker hgen hsurj z hz hz0
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hm' : ρ γ m - m = z γ := hm
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, Module.End.mul_apply]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm'.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm

end
