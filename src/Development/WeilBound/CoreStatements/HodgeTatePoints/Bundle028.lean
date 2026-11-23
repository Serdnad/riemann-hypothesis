module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace PositivityTheory.HtPt.Gi

theorem free_on_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c La _ _ EF N u h
  classical
  have := h.free
  have := h.finite
  let ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La) :=
    (Module.End.baseChangeHom ℤ C La).toRingHom.comp (Module.toModuleEnd ℤ La)
  have hρ : ∀ (a : 𝓞 E) (s : C) (x : La), ρ a (s ⊗ₜ x) = s ⊗ₜ (a • x) := fun a s x => rfl
  let e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C := LinearMap.BilinForm.baseChange C EF
  have he : ∀ (s t : C) (x y : La), e (s ⊗ₜ x) (t ⊗ₜ y) = (EF x y : C) * (s * t) := fun s t x y => by
    simp only [e, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul]
  have he1 : ∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C) := fun x y => by rw [he]; simp
  let T : Submodule O (C ⊗[ℤ] La) := Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x)
  have hT : ∀ x : La, (1 : C) ⊗ₜ[ℤ] x ∈ T := fun x => Submodule.subset_span ⟨x, rfl⟩
  let b := Module.Free.chooseBasis ℤ La
  let B := Algebra.TensorProduct.basis C b
  have hB : ∀ i, B i = 1 ⊗ₜ b i := fun i => Algebra.TensorProduct.basis_apply b i
  choose b' hb' using fun i => h.unimod.2 (b.coord i)
  have hrep : ∀ i y, e (1 ⊗ₜ b' i) y = B.repr y i := by
    intro i y
    have : e (1 ⊗ₜ b' i) = B.coord i := B.ext fun j => by
      rw [Module.Basis.coord_apply, B.repr_self, hB, he1, hb', Module.Basis.coord_apply, b.repr_self]
      simp only [Finsupp.single_apply]
      split_ifs <;> simp
    rw [this]; rfl
  have hskew : ∀ x y, EF x y = -EF y x := fun x y => by
    have := h.alt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h.alt] at this
    linarith
  have eskew : ∀ x y, e x y = -e y x := by
    intro x y
    induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
      | tmul t y => rw [he, he, hskew]; push_cast; ring
  have hTb : T = Submodule.span O (Set.range B) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      change (1 : C) ⊗ₜ[ℤ] x ∈ Submodule.span O (Set.range B)
      rw [← b.sum_repr x, tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [tmul_smul, ← hB]
      exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := B) i)) _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [hB]; exact hT _
  have hsp : Submodule.span C (T : Set (C ⊗[ℤ] La)) = ⊤ := by
    rw [hTb, Submodule.span_span_of_tower, B.span_eq]
  let w : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → C ⊗[ℤ] La := fun q =>
    ρ (RingOfIntegers.basis E q.2) (1 ⊗ₜ u q.1)
  have hTw : T = Submodule.span O (Set.range w) := by
    apply le_antisymm
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(p : O)}) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [hTb]; exact Submodule.fg_span (Set.finite_range B)
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨x, rfl⟩
        obtain ⟨a, x', rfl⟩ := h.span x
        change (1 : C) ⊗ₜ[ℤ] _ ∈ Submodule.span O (Set.range w) ⊔ Ideal.span {(p : O)} • T
        rw [tmul_add]
        refine Submodule.add_mem_sup ?_ ?_
        · rw [tmul_sum]
          refine Submodule.sum_mem _ fun i _ => ?_
          rw [← (RingOfIntegers.basis E).sum_repr (a i), Finset.sum_smul, tmul_sum]
          refine Submodule.sum_mem _ fun k _ => ?_
          rw [smul_assoc, tmul_smul]
          exact zsmul_mem (Submodule.subset_span (R := O) (Set.mem_range_self (f := w) (i, k))) _
        · rw [tmul_smul, ← Nat.cast_smul_eq_nsmul O]
          exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hT _)
    · rw [Submodule.span_le]
      rintro _ ⟨q, rfl⟩
      exact hT _
  refine ⟨ρ, T, e, fun a x => hρ a 1 x, rfl, ⟨?_, hsp, hTw⟩, he1, fun x => ?_, fun y hy => ?_, ?_, fun a x y => ?_⟩
  · refine linearIndependent_of_top_le_span_of_card_eq_finrank (b := w) ?_ ?_
    · rw [← hsp, hTw, Submodule.span_span_of_tower]
    · rw [Module.finrank_baseChange, h.rank, Fintype.card_prod, Fintype.card_fin,
        ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]
  · have := eskew x x
    have h2 : (2 : C) * e x x = 0 := by linear_combination this
    simpa using h2
  · exact B.ext_elem fun i => by rw [← hrep, hy]; simp
  · apply le_antisymm
    · intro y hy
      rw [hTb, ← B.sum_repr y]
      refine Submodule.sum_mem _ fun i _ => ?_
      obtain ⟨o, ho⟩ := hy _ (hT (b' i))
      rw [← hrep, ← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩ x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        exact ⟨(EF x y : O), by rw [he1, map_intCast]⟩
      | zero => simp
      | add x x' _ _ hx hx' =>
        rw [map_add (f := _), LinearMap.add_apply]; exact Subring.add_mem _ hx hx'
      | smul o x _ hx =>
        rw [← algebraMap_smul C o x, map_smul, LinearMap.smul_apply, smul_eq_mul]
        exact Subring.mul_mem _ ⟨o, rfl⟩ hx
  · induction x with
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | tmul s x =>
      induction y with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul t y => rw [hρ, hρ, he, he, h.adj]

end PositivityTheory.HtPt.Gi
end

section

noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem finrank_int_eq {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] :
    Module.finrank ℤ M = Module.finrank (𝓞 E) M * Module.finrank ℚ E := by
  set S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)
  have hS : S ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by
      simpa using (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)).ne (nonZeroDivisors.ne_zero hn))
  let f := TensorProduct.mk (𝓞 E) E M 1
  haveI hloc : IsLocalizedModule S f :=
    (isLocalizedModule_iff_isBaseChange S E f).mpr (TensorProduct.isBaseChange (𝓞 E) M E)
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars (nonZeroDivisors ℤ) f
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (f.restrictScalars ℤ) le_rfl
  have h2 := IsLocalizedModule.finrank_eq S f hS
  have h3 := IsLocalization.finrank_eq E S hS (N := TensorProduct (𝓞 E) E M)
  have h4 := IsFractionRing.finrank_right_eq ℤ ℚ (TensorProduct (𝓞 E) E M)
  have h5 := Module.finrank_mul_finrank ℚ E (TensorProduct (𝓞 E) E M)
  rw [← h1, ← h4, ← h5, h3, h2, mul_comm]

private theorem exists_span_sup_maximal_smul_eq_top {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsMaximal]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ m : Fin (Module.finrank R M) → M, Submodule.span R (Set.range m) ⊔ P • ⊤ = ⊤ := by
  classical
  let Rp := Localization.AtPrime P
  let f := TensorProduct.mk R Rp M 1
  haveI hloc : IsLocalizedModule P.primeCompl f :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl Rp f).mpr (TensorProduct.isBaseChange R M Rp)
  have hle : P.primeCompl ≤ nonZeroDivisors R := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ P.zero_mem))
  have hrank : Module.finrank Rp (TensorProduct R Rp M) = Module.finrank R M :=
    (IsLocalization.finrank_eq Rp P.primeCompl hle).trans (IsLocalizedModule.finrank_eq P.primeCompl f hle)
  haveI : Module.Free Rp (TensorProduct R Rp M) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq Rp (TensorProduct R Rp M) hrank
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective P.primeCompl f (b i)
  refine ⟨fun i => (ms i).1, ?_⟩
  set N := Submodule.span R (Set.range fun i => (ms i).1)
  have htop : Submodule.localized' Rp P.primeCompl f N = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (Submodule.mem_localized' Rp P.primeCompl f N _).mpr
      ⟨(ms i).1, Submodule.subset_span ⟨i, rfl⟩, (ms i).2, hms i⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, t, hyt⟩ := (Submodule.mem_localized' Rp P.primeCompl f N (f x)).mp (htop ▸ Submodule.mem_top)
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hyt
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) hyt
  have hmem : ((c : R) * t) • x ∈ N := by
    rw [mul_smul, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]
    exact N.smul_mem _ hy
  have hnot : (c : R) * t ∉ P := (P.primeCompl.mul_mem c.2 t.2)
  obtain ⟨r, i, hi, hri⟩ := hP.exists_inv hnot
  have : x = (r * ((c : R) * t)) • x + i • x := by rw [← add_smul, hri, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (by rw [mul_smul]; exact N.smul_mem r hmem))
    (Submodule.mem_sup_right (Submodule.smul_mem_smul hi Submodule.mem_top))

private theorem exists_finrank_family_mod_smul {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (hn : Module.finrank R M = n) (a : R) (ha : a ≠ 0) :
    ∃ u : Fin n → M, ∀ x : M, ∃ (c : Fin n → R) (x' : M), x = ∑ i, c i • u i + a • x' := by
  classical
  subst hn
  set F := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hm : ∀ P ∈ F, ∃ m : Fin (Module.finrank R M) → M,
      Submodule.span R (Set.range m) ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    haveI : P.IsMaximal := Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P hP))
      (by rw [← Ideal.zero_eq_bot]; exact (hprime P hP).ne_zero)
    exact exists_span_sup_maximal_smul_eq_top P M
  choose! m hm using hm
  have he : ∀ Q ∈ F, ∃ e : R, ∀ P ∈ F, e - (if P = Q then 1 else 0) ∈ P := by
    intro Q _
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := F) id (fun _ => 1)
      (fun i hi => hprime i hi) (fun i _ j _ h => h) (fun P => if P.1 = Q then 1 else 0)
    exact ⟨y, fun P hP => by simpa using hy P hP⟩
  choose! e he using he
  let u : Fin (Module.finrank R M) → M := fun i => ∑ Q ∈ F, e Q • m Q i
  have hdiff : ∀ P ∈ F, ∀ i, u i - m P i ∈ P • (⊤ : Submodule R M) := by
    intro P hP i
    have : u i - m P i = ∑ Q ∈ F, (e Q - if P = Q then 1 else 0) • m Q i := by
      simp only [u, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, hP, if_true]
    rw [this]
    exact Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem_smul (he Q hQ P hP) Submodule.mem_top
  set N := Submodule.span R (Set.range u) ⊔ Ideal.span {a} • (⊤ : Submodule R M)
  have hcov : ∀ P ∈ F, N ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    refine eq_top_iff.mpr ((hm P hP).symm.le.trans (sup_le ?_ le_sup_right))
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : m P i = u i - (u i - m P i) := by abel
    rw [this]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
      (Submodule.mem_sup_right (hdiff P hP i))
  have key : ∀ I J : Ideal R, N ⊔ I • (⊤ : Submodule R M) = ⊤ → N ⊔ J • (⊤ : Submodule R M) = ⊤ →
      N ⊔ (I * J) • (⊤ : Submodule R M) = ⊤ := by
    intro I J hI hJ
    refine eq_top_iff.mpr (hI.symm.le.trans (sup_le le_sup_left ?_))
    rw [Submodule.mul_smul]
    calc I • (⊤ : Submodule R M) = I • (N ⊔ J • ⊤) := by rw [hJ]
      _ = I • N ⊔ I • J • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ N ⊔ I • J • ⊤ := sup_le_sup_right (Submodule.smul_le_right) _
  have hfac : ∀ s : Multiset (Ideal R), (∀ P ∈ s, P ∈ F) → N ⊔ s.prod • (⊤ : Submodule R M) = ⊤ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons P s ih =>
      intro h
      rw [Multiset.prod_cons]
      exact key _ _ (hcov P (h P (Multiset.mem_cons_self _ _)))
        (ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ))
  have hN : N = ⊤ := by
    have := hfac (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))
      (fun P hP => Multiset.mem_toFinset.mpr hP)
    rwa [Ideal.prod_normalizedFactors_eq_self (by simpa using ha), sup_eq_left.mpr le_sup_right] at this
  refine ⟨u, fun x => ?_⟩
  have hx : x ∈ N := hN ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨x', _, rfl⟩ := hz
  exact ⟨c, x', rfl⟩

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem pol_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime], ∃ u : Fin (D.p + D.q) → D.La, IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u := by
  intro E _ _ _ H D p _
  haveI := D.fin
  haveI := D.proj
  have hfinZ : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance
  haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)
  obtain ⟨u, hu⟩ := exists_finrank_family_mod_smul D.La (D.p + D.q) D.rank (p : 𝓞 E)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨u, ⟨inferInstance, hfinZ, D.alt, D.unimod, ?_, ?_, ?_⟩⟩
  · intro a x y
    rw [D.adj]
    congr 2
    ext
    simp [H.bar_eq]
  · rw [finrank_int_eq (E := E), D.rank]
  · intro x
    obtain ⟨a, x', hx⟩ := hu x
    exact ⟨a, x', by rw [hx, Nat.cast_smul_eq_nsmul]⟩

end PositivityTheory.HtPt.Htat
end
end
