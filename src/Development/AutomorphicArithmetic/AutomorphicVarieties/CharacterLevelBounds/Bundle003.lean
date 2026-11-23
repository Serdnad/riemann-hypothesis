module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Mathlib.RingTheory.Length
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.GaloisCohomology.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem exists_reps {G : Type} [Group G] (U' U : Subgroup G) (h0 : U'.relIndex U ≠ 0) :
    ∃ T : Finset G, (T : Set G) ⊆ U ∧ T.card ≤ U'.relIndex U ∧ U ≤ Subgroup.closure (T : Set G) ⊔ U' := by
  classical
  set K : Subgroup U := U'.subgroupOf U with hK
  have hfi : K.FiniteIndex := ⟨by rw [hK]; exact h0⟩
  haveI : Finite (U ⧸ K) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (U ⧸ K) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨q, rfl⟩ := hx
    exact (Quotient.out q).2
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Subgroup.relIndex, ← hK, Subgroup.index]
  · intro u hu
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (⟨u, hu⟩ : U)
    have hkU' : ((k : U) : G) ∈ U' := Subgroup.mem_subgroupOf.mp k.2
    have hout : ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) ∈ Subgroup.closure
        ((Finset.univ.image (fun q : U ⧸ K => ((Quotient.out q : U) : G)) : Finset G) : Set G) := by
      apply Subgroup.subset_closure
      simp
    have heq : u = ((Quotient.out (QuotientGroup.mk (⟨u, hu⟩ : U) : U ⧸ K) : U) : G) * ((k : U) : G)⁻¹ := by
      have := congrArg (fun x : U => (x : G)) hk
      simp only [Subgroup.coe_mul] at this
      rw [this]; group
    rw [heq]
    exact Subgroup.mul_mem_sup hout (U'.inv_mem hkU')

theorem UpperTheory.V.Chr.kerIdx :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* Oˣ), ContAction (twist₂ l θ) →
          ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ n : ℕ, n ≠ 0 → U'.relIndex U ∣ n →
          Module.length O (LinearMap.ker (resU (twist₂ l θ) h)) ≤ (n : ℕ∞) * Module.length O (H0U (twist₂ l θ) U) := by
  intro l _ O _ _ _ _ _ G _ _ _ θ hθ U' U h hab n hn hd
  obtain ⟨T, hT, hc, hU⟩ := exists_reps U' U (ne_zero_of_dvd_ne_zero hn hd)
  have key := UpperTheory.V.Base.kerResAb O G (QO l O) (twist₂ l θ) hθ (UpperTheory.V.Base.qoFacts l O).1
    (fun g => ⟨((θ g : Oˣ) : O), fun _ => rfl⟩) U' U h hab T hT (hU.trans (Subgroup.le_topologicalClosure _))
  refine key.trans ?_
  have : (T.card : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast hc.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
  gcongr
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (h : ζ ^ n = 1) (h1 : ζ ≠ 1) :
    ζ - 1 ∣ (n : O) := by
  have hS : ∑ i ∈ Finset.range n, ζ ^ i = 0 := by
    have hg := mul_geom_sum ζ n
    rw [h, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_left (sub_ne_zero.mpr h1)
  have hn : (n : O) = ∑ i ∈ Finset.range n, (1 - ζ ^ i) := by
    rw [Finset.sum_sub_distrib, hS, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
  rw [hn]
  apply Finset.dvd_sum
  intro i _
  have hd := sub_dvd_pow_sub_pow ζ 1 i
  rw [one_pow] at hd
  rw [← neg_sub (ζ ^ i) 1]
  exact (dvd_neg).mpr hd

theorem UpperTheory.V.Chr.rootVal :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (n : ℕ), n ≠ 0 → IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O ∧
          (∀ ζ : O, ζ ^ n = 1 → ζ ≠ 1 → IsDiscreteValuationRing.addVal O (ζ - 1) ≤ (n.factorization l : ℕ∞) * eO l O) ∧ eO l O ≠ ⊤ ∧ CharZero O := by
  intro l _ O _ _ _ _ _ n hn
  obtain ⟨hiO, -, -, -, -, -, -, hvO, hunit⟩ := dvrFacts l O
  have hp : l.Prime := Fact.out
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hlO : (l : O) ≠ 0 := by
    intro h
    apply hl0
    apply hiO
    rw [map_natCast, h, map_zero]
  have hval : IsDiscreteValuationRing.addVal O (n : O) = (n.factorization l : ℕ∞) * eO l O := by
    have hu : IsUnit ((n / l ^ n.factorization l : ℕ) : O) := hunit _ (Nat.not_dvd_ordCompl hp hn)
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n l]
    rw [Nat.cast_mul, Nat.cast_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hu,
      add_zero, hvO, nsmul_eq_mul]
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro ζ hζ h1
    rw [← hval]
    exact (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (sub_one_dvd hζ h1)
  · rw [hvO]
    exact fun h => hlO ((IsDiscreteValuationRing.addVal_eq_top_iff).mp h)
  · exact charZero_of_injective_algebraMap hiO
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem selFam_length_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict (Submodule.subtype_injective _)
    f.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective _ (Submodule.subtype_injective _))

private theorem selFam_abs {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] {ι : Type} [Fintype ι]
    {Y Z : ι → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)] [∀ i, AddCommGroup (Z i)] [∀ i, Module R (Z i)]
    (A B : Submodule R X) (p : ∀ i, X →ₗ[R] Y i) (q : ∀ i, Y i →ₗ[R] Z i)
    (h1 : ∀ i, ∀ x ∈ A, q i (p i x) = 0) (h2 : ∀ x ∈ A, (∀ i, p i x = 0) → x ∈ B) :
    Module.length R A ≤ Module.length R B + ∑ i, Module.length R (LinearMap.ker (q i)) := by
  let f : A →ₗ[R] (∀ i, LinearMap.ker (q i)) :=
    LinearMap.pi fun i => LinearMap.codRestrict _ ((p i).comp A.subtype) (fun x => h1 i x.1 x.2)
  have hk : ∀ x : LinearMap.ker f, (A.subtype.comp (LinearMap.ker f).subtype) x ∈ B := fun x =>
    h2 x.1.1 x.1.2 fun i => congrArg Subtype.val (congrFun (LinearMap.mem_ker.1 x.2) i)
  have := selFam_length_le f (LinearMap.codRestrict _ _ hk) (by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1))
  rwa [Module.length_pi_of_fintype] at this

private theorem selFam_conj {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R G M)
    (U D D' : Subgroup G) (u : G) (hu : u ∈ U) (hux : ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D) (z : Z1U ρ U)
    (hi : resU ρ (inf_le_left : U ⊓ D ≤ U) (Submodule.Quotient.mk z) = 0) :
    ∃ m, ∀ x : U, x.1 ∈ D' → z.1 x = ρ x m - m := by
  obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ _ z).1 hi
  refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun x hx => ?_⟩
  have hy : u⁻¹ * x.1 * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) x.2) hu
  have h1 : z.1 ⟨u⁻¹ * x.1 * u, hy⟩ = ρ (u⁻¹ * x.1 * u) m - m := hm ⟨_, hy, hux x.1 ⟨x.2, hx⟩⟩
  have e1 : (⟨u, hu⟩ : U) * ⟨_, hy⟩ = x * ⟨u, hu⟩ := Subtype.ext (by simp [mul_assoc])
  have e2 := congrArg z.1 e1
  rw [z.2.2, z.2.2] at e2
  have e3 : z.1 ⟨u, hu⟩ + ρ u (z.1 ⟨_, hy⟩) = z.1 x + ρ x (z.1 ⟨u, hu⟩) := e2
  have e4 : ρ u (ρ (u⁻¹ * x.1 * u) m) = ρ x (ρ u m) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  rw [h1, map_sub, e4] at e3
  rw [eq_sub_of_add_eq e3.symm, map_sub]
  abel

theorem UpperTheory.V.Chr.selFam :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
          [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U : Subgroup G) (𝒟 𝒟' : Set (Subgroup G)) (ι : Type) [Fintype ι] (I D : ι → Subgroup G) (h : ∀ i, I i ≤ D i),
          (∀ i, I i ∈ 𝒟) → (∀ D' ∈ 𝒟', D' ∈ 𝒟 ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
          Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U 𝒟') +
            ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_left U (h i)))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U 𝒟 𝒟' ι _ I D h hI hc
  refine selFam_abs (LocSel ρ U 𝒟) (LocSel ρ U 𝒟') (fun i => resU ρ (inf_le_left : U ⊓ D i ≤ U))
    (fun i => resU ρ (inf_le_inf_left U (h i))) (fun i x hx => ?_) (fun x hx hi => ?_)
  · exact (resU_resU ρ _ _ x).trans (mem_locSel.1 hx (I i) (hI i))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine mk_mem_locSel.2 fun D' hD' => ?_
    rcases hc D' hD' with hle | ⟨i, u, hu, hux⟩
    · exact mk_mem_locSel.1 hx D' hle
    · exact selFam_conj ρ U (D i) D' u hu hux z (hi i)
end
