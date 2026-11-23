module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Mathlib.Algebra.DualNumber
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle004
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem hom_eq_res (g : R →ₐ[O] ResidueField O) (x : R) : g x = res O R x := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap O R a, by rw [g.commutes, IsLocalRing.ResidueField.algebraMap_eq]⟩
  have hker : RingHom.ker (g : R →+* ResidueField O) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 : g (x - algebraMap O R a) = 0 := by
    have hm : x - algebraMap O R a ∈ RingHom.ker (g : R →+* ResidueField O) := by
      rw [hker]
      exact ha
    exact (RingHom.mem_ker).1 hm
  have h2 : res O R (x - algebraMap O R a) = 0 := (res_eq_zero_iff O R _).2 ha
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, AlgHom.commutes, AlgHom.commutes]

private theorem tan_mul (D : Tan O R) (f g : R) :
    D.1 (f * g) = res O R f * D.1 g + res O R g * D.1 f := D.2 f g

private theorem tan_one (D : Tan O R) : D.1 1 = 0 := by
  simpa using tan_mul D 1 1

private theorem tan_alg (D : Tan O R) (a : O) : D.1 (algebraMap O R a) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, tan_one, smul_zero]

private theorem tan_finite : Module.Finite (ResidueField O) (Tan O R) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R) : (maximalIdeal R).FG)
  let φ : Tan O R →ₗ[ResidueField O] (s → ResidueField O) :=
    { toFun := fun D i => D.1 (i : R)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective φ ((injective_iff_map_eq_zero φ).2 fun D hD => ?_)
  have h0 : ∀ i ∈ s, D.1 i = 0 := fun i hi => congrFun hD ⟨i, hi⟩
  have hm : ∀ y ∈ maximalIdeal R, D.1 y = 0 := by
    intro y hy
    rw [← hs] at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h0 z hz
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
    | smul c z hz ih =>
      have hz' : z ∈ maximalIdeal R := by
        rw [← hs]
        exact hz
      rw [smul_eq_mul, tan_mul, ih, (res_eq_zero_iff O R z).2 hz', mul_zero, zero_mul, add_zero]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h := hm _ ha
  rw [map_sub, tan_alg, sub_zero] at h
  exact h

private noncomputable def tanEquiv : (R →ₐ[O] DualNumber (ResidueField O)) ≃ Tan O R where
  toFun f := ⟨{ toFun := fun x => (f x).snd
                map_add' := fun x y => by simp
                map_smul' := fun a x => by simp }, fun x y => by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    show (f (x * y)).snd = res O R x • (f y).snd + res O R y • (f x).snd
    rw [map_mul, DualNumber.snd_mul, h, h, smul_eq_mul, smul_eq_mul, mul_comm (f x).snd]⟩
  invFun D :=
    { toFun := fun x => TrivSqZeroExt.inl (res O R x) + TrivSqZeroExt.inr (D.1 x)
      map_one' := by ext <;> simp [tan_one]
      map_mul' := fun x y => by ext <;> simp [tan_mul, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp
      commutes' := fun a => by
        ext
        · simp [TrivSqZeroExt.algebraMap_eq_inl']
        · simp [tan_alg, TrivSqZeroExt.algebraMap_eq_inl'] }
  left_inv f := by
    have h : ∀ z, (f z).fst = res O R z := fun z =>
      hom_eq_res ((TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).comp f) z
    refine AlgHom.ext fun x => ?_
    ext <;> simp [h]
  right_inv D := Subtype.ext (LinearMap.ext fun x => by simp)

end

theorem UpperTheory.V.Fr.pr_tan :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R], Module.Finite (ResidueField O) (Tan O R) ∧ Nat.card (R →ₐ[O] (DualNumber (ResidueField O))) = Nat.card (Tan O R) := by
  intro O _ _ R _ _ _
  exact ⟨tan_finite, Nat.card_congr tanEquiv⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem adicCont_ringHom_comp_of_map_mem {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S]
    {I : Ideal R} {J : Ideal S} (f : R →+* S) (hIJ : ∀ x ∈ I, f x ∈ J) {u : Γ → R}
    (hu : AdicCont I u) : AdicCont J fun g => f (u g) := by
  intro N
  have hle : I ^ N ≤ (J ^ N).comap f := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) N
  have hc := (hu N).comp (Ideal.quotientMap (J ^ N) f hle)
  convert hc using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Fr.alg_lift :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsModel O C 𝔪 ρ → ∀ (Q : Type) [CommRing Q] [Algebra O Q] [IsCO O Q] (p : D →ₐ[O] Q), (∀ x ∈ 𝔪, p x ∈ maximalIdeal Q) → IsLift O (ρ.map (p : D →+* Q)) := by
  intro l _ O _ _ F n C _ _ _ D _ _ _ _ 𝔪 ρ hm Q _ _ _ p hp
  have hres : ∀ c : C, res O Q (p (algebraMap C D c)) = res O C c := fun c =>
    res_map (p.comp (IsScalarTower.toAlgHom O C D)) c
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.1 i j)
  · exact adicCont_ringHom_comp_of_map_mem (p : D →+* Q) hp (hm.cont.2 v i)
  · obtain ⟨c, hc1, hc2⟩ := hm.dg g i
    show res O Q (p (ρ.r g i i)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · obtain ⟨c, hc1, hc2⟩ := hm.psi v i g
    show res O Q (p ↑(ρ.ψ v i g)) = _
    rw [← hc1, hres, hc2, RingHom.id_apply]
  · show res O Q (p (ρ.r g i j)) = 0
    rw [res_eq_zero_iff]
    exact hp _ (hm.off g i j hij)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem UpperTheory.V.Fr.single_coeff_mul {K : Type} [CommRing K] (p q : AddMonoidAlgebra K ℤ) (j : ℤ) :
    AddMonoidAlgebra.single j ((p * q).coeff j) = ∑ a ∈ p.coeff.support,
      AddMonoidAlgebra.single a (p.coeff a) * AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) := by
  classical
  have key : ∀ a : ℤ, AddMonoidAlgebra.single a (p.coeff a) *
      AddMonoidAlgebra.single (-a + j) (q.coeff (-a + j)) =
        AddMonoidAlgebra.single j (p.coeff a * q.coeff (-a + j)) := by
    intro a
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
  simp_rw [key]
  have hc : (p * q).coeff j = ∑ a ∈ p.coeff.support, p.coeff a * q.coeff (-a + j) := by
    rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.sum]
    have hcond : ∀ b : ℤ, (a + b = j) ↔ (b = -a + j) := fun b => by omega
    simp_rw [hcond]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [Finsupp.notMem_support_iff.mp hm, mul_zero]
  rw [hc]
  ext k
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  split_ifs with hk
  · rfl
  · simp

theorem UpperTheory.V.Fr.alg_homog :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
      {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (N : ℕ) (p : lauSub P),
      p ∈ vertex h ^ N → ∀ j : ℤ,
        (⟨AddMonoidAlgebra.single j (p.1.coeff j), single_mem_lauSub P (p.2 j)⟩ : lauSub P) ∈
          vertex h ^ N := by
  intro C K _ _ _ _ P _ h N
  let comp : lauSub P → ℤ → lauSub P := fun q k =>
    ⟨AddMonoidAlgebra.single k (q.1.coeff k), single_mem_lauSub P (q.2 k)⟩
  have hcomp : ∀ q k, (comp q k).1 = AddMonoidAlgebra.single k (q.1.coeff k) := fun _ _ => rfl
  have base : ∀ q : lauSub P, q ∈ vertex h → ∀ k : ℤ, comp q k ∈ vertex h := by
    intro q hq k
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = q.1.coeff 0 at hq
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp q k).1.coeff 0
    obtain ⟨c, hc, hce⟩ := hq
    rw [hcomp, AddMonoidAlgebra.coeff_single]
    by_cases hk : k = 0
    · subst hk
      exact ⟨c, hc, by rw [Finsupp.single_eq_same, hce]⟩
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hk, map_zero]⟩
  show ∀ p : lauSub P, p ∈ vertex h ^ N → ∀ j, comp p j ∈ vertex h ^ N
  induction N with
  | zero =>
    intro p _ j
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ n ih =>
    intro p hp
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on (C := fun r => ∀ j, comp r j ∈ vertex h ^ (n + 1)) hp ?_ ?_
    · intro x hx y hy j
      have e : comp (x * y) j =
          ∑ a ∈ x.1.coeff.support, comp x a * comp y (-a + j) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum, hcomp, Subalgebra.coe_mul, single_coeff_mul]
        rfl
      rw [e, pow_succ]
      exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih x hx a) (base y hy _)
    · intro x y hx hy j
      have e : comp (x + y) j = comp x j + comp y j := by
        apply Subtype.ext
        simp only [hcomp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          AddMonoidAlgebra.single_add]
      rw [e]
      exact add_mem (hx j) (hy j)
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem single_mem_of_span {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (A : Subalgebra C (AddMonoidAlgebra K ℤ)) (j : ℤ) (s : Set K)
    (hs : ∀ x ∈ s, AddMonoidAlgebra.single j x ∈ A) {x : K} (hx : x ∈ Submodule.span C s) :
    AddMonoidAlgebra.single j x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hs y hy
  | zero => rw [AddMonoidAlgebra.single_zero]; exact A.zero_mem
  | add y z _ _ hy hz => rw [AddMonoidAlgebra.single_add]; exact A.add_mem hy hz
  | smul c y _ hy => rw [← AddMonoidAlgebra.smul_single]; exact A.smul_mem hy c

theorem UpperTheory.V.Fr.alg_ft :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} (C : Type) [CommRing C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), (∀ i j, (Submodule.span C (Set.range fun g => ρ.r g i j)).FG) → Algebra.FiniteType C (lauSub (ρ.part C)) := by
  intro l _ k _ F n C _ K _ _ ρ h
  choose S hS using h
  set G : Set (AddMonoidAlgebra K ℤ) :=
    ⋃ i, ⋃ j, (fun x => AddMonoidAlgebra.single (w n i - w n j) x) '' (S i j : Set K) with hG
  have hGfin : G.Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => (S i j).finite_toSet.image _
  have hGmem : ∀ i j x, x ∈ (S i j : Set K) →
      AddMonoidAlgebra.single (w n i - w n j) x ∈ Algebra.adjoin C G := fun i j x hx =>
    Algebra.subset_adjoin (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨x, hx, rfl⟩⟩⟩)
  have hent : ∀ g i j, AddMonoidAlgebra.single (w n i - w n j) (ρ.r g i j) ∈ Algebra.adjoin C G :=
    fun g i j => single_mem_of_span (Algebra.adjoin C G) _ (S i j) (hGmem i j)
      (by rw [hS i j]; exact Submodule.subset_span ⟨g, rfl⟩)
  have hlist : ∀ L : List (F.G0 × Fin n × Fin n),
      AddMonoidAlgebra.single ((L.map fun s => w n s.2.1 - w n s.2.2).sum)
        ((L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod) ∈ Algebra.adjoin C G := by
    intro L
    induction L with
    | nil =>
      simp only [List.map_nil, List.sum_nil, List.prod_nil]
      rw [← AddMonoidAlgebra.one_def]
      exact (Algebra.adjoin C G).one_mem
    | cons s L ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      rw [← AddMonoidAlgebra.single_mul_single]
      exact mul_mem (hent _ _ _) ih
  have hmon : ∀ j, ∀ x ∈ ρ.mon j, AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G := by
    rintro j x ⟨L, hL, rfl⟩
    rw [← hL]
    exact hlist L
  have hpart : ∀ j x, x ∈ ρ.part C j → AddMonoidAlgebra.single j x ∈ Algebra.adjoin C G :=
    fun j x hx => single_mem_of_span _ j _ (hmon j) hx
  have heq : Algebra.adjoin C G = lauSub (ρ.part C) := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      intro y hy
      obtain ⟨i, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply single_mem_lauSub
      have hx' : x ∈ Submodule.span C (Set.range fun g => ρ.r g i j) := by
        rw [← hS i j]
        exact Submodule.subset_span hx
      refine Submodule.span_le.mpr ?_ hx'
      rintro _ ⟨g, rfl⟩
      exact NRep.r_mem_part C ρ g i j
    · intro p hp
      have hp' : ∀ j, p.coeff j ∈ ρ.part C j := hp
      have hsum : p = p.coeff.sum fun j x => AddMonoidAlgebra.single j x := by
        apply AddMonoidAlgebra.ext
        rw [Finsupp.sum, AddMonoidAlgebra.coeff_sum]
        exact (Finsupp.sum_single _).symm
      rw [hsum]
      exact Subalgebra.sum_mem _ fun j _ => hpart j _ (hp' j)
  exact ⟨(Subalgebra.fg_top _).mpr ⟨hGfin.toFinset, by rw [Set.Finite.coe_toFinset]; exact heq⟩⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_closed :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ c : ℕ → C, (∀ N, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1)) → ∃ x : C, ∀ N, algebraMap C D (x - c N) ∈ 𝔪 ^ (N + 1) := by
  intro C _ _ _ _ D _ _ 𝔪 h c hc
  let J : ℕ → Ideal C := fun n => (𝔪 ^ n).comap (algebraMap C D)
  have hJ : Antitone J := fun _ _ hab => Ideal.comap_mono (Ideal.pow_le_pow_right hab)
  have h0 : ⨅ n, J n = ⊥ := by
    simp only [J]
    rw [← Ideal.comap_iInf, h.sep, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
    exact h.inj
  choose s hs using GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot J hJ h0
  have hd : ∀ N d, c (N + d) - c N ∈ J (N + 1) := fun N d => by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : c (N + d + 1) - c (N + d) ∈ J (N + 1) := hJ (show N + 1 ≤ N + d + 1 by omega) (hc (N + d))
      have := (J (N + 1)).add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  have hle : ∀ {a b}, a ≤ b → c b - c a ∈ J (a + 1) := fun {a b} hab => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact hd a d
  let t : ℕ → ℕ := fun k => k + ∑ i ∈ Finset.range (k + 1), s i
  have ht : ∀ k, s k ≤ t k := fun k => by
    simp only [t, Finset.sum_range_succ]
    omega
  have ht' : ∀ k, k ≤ t k := fun k => Nat.le_add_right _ _
  have htm : Monotone t := fun a b hab =>
    Nat.add_le_add hab (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal C) (fun k => c (t k)) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact hs m (hJ (by have := ht m; omega) (hle (htm hmn)))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun N => ?_⟩
  have h1 : c (t (N + 1)) - L ∈ J (N + 1) := by
    have := hL (N + 1)
    rw [← h.comap] at this
    exact Ideal.le_comap_pow _ (N + 1) this
  have h2 : c (t (N + 1)) - c N ∈ J (N + 1) := hle (by have := ht' (N + 1); omega)
  have h3 := (J (N + 1)).sub_mem h2 h1
  rwa [sub_sub_sub_cancel_left] at h3
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cor_mul {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : A 0 1 = 0) (h2 : A 2 1 = 0) :
    (A * B).submatrix cor cor = A.submatrix cor cor * B.submatrix cor cor := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [cor, h0, h2]

private theorem mid_mul' {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : B 0 1 = 0) (h2 : B 2 1 = 0) :
    (A * B) 1 1 = A 1 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h2]

private theorem cor_one' {K : Type} [CommRing K] :
    (1 : Matrix (Fin 3) (Fin 3) K).submatrix cor cor = 1 :=
  Matrix.submatrix_one _ (by decide)

private theorem cor_sub {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) (t : K) :
    (A - t • (1 : Matrix (Fin 3) (Fin 3) K)).submatrix cor cor = A.submatrix cor cor - t • 1 := by
  simp [Matrix.submatrix_sub, Matrix.submatrix_smul, cor_one']

private theorem cor_J {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) :
    (Jmat (R := K) 3 * Aᵀ * Jmat (R := K) 3).submatrix cor cor =
      Jmat (R := K) 2 * (A.submatrix cor cor)ᵀ * Jmat (R := K) 2 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, cor, Fin.rev]

private theorem ordProd_three {H K : Type} [CommRing K] (r : H → Matrix (Fin 3) (Fin 3) K) (ψ : Fin 3 → H → K)
    (x y z : H) : ordProd r ψ ![x, y, z] =
      (r x - ψ 0 x • 1) * (r y - ψ 1 y • 1) * (r z - ψ 2 z • 1) := by
  simp [ordProd, List.ofFn_succ, mul_assoc]

private theorem ordProd_two {H K : Type} [CommRing K] (r : H → Matrix (Fin 2) (Fin 2) K) (ψ : Fin 2 → H → K)
    (g : Fin 2 → H) : ordProd r ψ g = (r (g 0) - ψ 0 (g 0) • 1) * (r (g 1) - ψ 1 (g 1) • 1) := by
  simp [ordProd, List.ofFn_succ]

theorem UpperTheory.V.Fr.exists_frobenius_corner :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K), (∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) → CornerUnits ρ → ∃ σ : NRep F 2 K, IsCorner ρ σ := by
  intro l _ k _ F K _ ρ hodd hU
  have hc : ∀ g (i : Fin 3), i ≠ 1 → ρ.r g i 1 = 0 := by
    intro g i hi
    apply hodd
    fin_cases i <;> simp_all [w, Int.odd_iff]
  have hcs : ∀ g (t : K) (i : Fin 3), i ≠ 1 → (ρ.r g - t • 1) i 1 = 0 := by
    intro g t i hi
    rw [Matrix.sub_apply, Matrix.smul_apply, hc g i hi, Matrix.one_apply_ne hi, smul_zero, sub_zero]
  have hinj : Function.Injective cor := by decide
  let s : F.G0 →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => (ρ.r g).submatrix cor cor
      map_one' := by simp only [map_one, cor_one']
      map_mul' := fun a b => by
        simp only [map_mul]
        exact cor_mul _ _ (hc a 0 (by decide)) (hc a 2 (by decide)) }
  refine ⟨⟨s, fun v i => ρ.ψ v (cor i), ?_, ?_, ?_⟩, ?_⟩
  · intro g
    show (ρ.r (F.star g)).submatrix cor cor =
      Jmat (R := K) 2 * ((ρ.r g).submatrix cor cor)ᵀ * Jmat (R := K) 2
    rw [ρ.pol, cor_J]
  · intro i j hij
    have hd := ρ.diag (cor i) (cor j) (hinj.ne hij)
    rw [Matrix.sub_apply] at hd ⊢
    exact hd
  · intro v g
    obtain ⟨g₁, -, -, u1⟩ := hU v
    have key := frobenius_corner_order_skips (s.comp (F.loc0 v)) (fun x => (ρ.ψ v 0 x : K)) ((Units.coeHom K).comp (ρ.ψ v 2)) g₁ (ρ.ψ v 1 g₁ : K) ?det ?three (g 0) (g 1)
    · rw [ordProd_two]
      exact key
    · show IsUnit ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1).det
      rw [← cor_sub, Matrix.det_fin_two]
      simpa [cor, Matrix.one_apply] using u1
    · intro x y
      show ((ρ.r (F.loc0 v x)).submatrix cor cor - (ρ.ψ v 0 x : K) • 1) * ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1) * ((ρ.r (F.loc0 v y)).submatrix cor cor - (ρ.ψ v 2 y : K) • 1) = 0
      have h3 := ρ.ord v ![x, g₁, y]
      rw [ordProd_three] at h3
      beta_reduce at h3
      rw [← cor_sub, ← cor_sub, ← cor_sub, mul_assoc, ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← mul_assoc, h3, Matrix.submatrix_zero]
      rfl
  · refine ⟨hodd, fun g i j => rfl, fun v i g => rfl, fun v g => ?_⟩
    obtain ⟨g₁, u0, u2, -⟩ := hU v
    have h3 := ρ.ord v ![g₁, g, g₁]
    rw [ordProd_three] at h3
    beta_reduce at h3
    have h11 := congrFun (congrFun h3 1) 1
    rw [mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide))] at h11
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h11
    rw [u2.mul_left_eq_zero, u0.mul_right_eq_zero, sub_eq_zero] at h11
    exact h11
end
