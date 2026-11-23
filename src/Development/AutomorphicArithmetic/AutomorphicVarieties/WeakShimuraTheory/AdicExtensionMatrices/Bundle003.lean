module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle007
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
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtGr0 :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.gr 0 →ₐ[Λ] R'), (∀ (b : W.gr 0) (n : W.σ →₀ ℕ), Finsupp.weight W.wt n = 0 → ((b : W.A) : R) = (n.prod fun s k => W.z s ^ k) → f b = f' b) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ R' _ _ _ f f' h
  obtain ⟨-, u, hu, hm⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hloc : ∀ g : W.gr 0 →ₐ[Λ] R', ∀ x ∈ maximalIdeal (W.gr 0), g x ∈ maximalIdeal R' := fun g x hx => by
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hx
  refine UpperTheory.V.Alg.co_ext Λ (W.gr 0) Λ R' (maximalIdeal R') (Algebra.ofId Λ (W.gr 0)) (u : Set (W.gr 0)) ?_ ?_ f f'
    ⟨1, fun x hx => ?_⟩ (Subsingleton.elim _ _) fun s hs => ?_
  · intro b hb
    show b ∈ maximalIdeal (W.gr 0)
    rw [hm]
    exact Ideal.mem_sup_right (Ideal.subset_span hb)
  · refine le_trans (hm.trans (sup_comm _ _)).le ?_
    exact le_sup_left
  · rw [pow_one] at hx
    exact ⟨hloc f x hx, hloc f' x hx⟩
  · obtain ⟨n, -, hn, hb⟩ := hu s hs
    exact h s n hn hb
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.sxContGr_pow {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (n : ℕ) :
    ∀ x ∈ Q ^ n, ∃ y ∈ J ^ n, e y = x := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, Submodule.one_eq_range] at hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨algebraMap Λ K a, by simp, e.commutes a⟩
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := ih a ha
      obtain ⟨v, hv, rfl⟩ := hQ b hb
      exact ⟨u * v, by rw [pow_succ]; exact Ideal.mul_mem_mul hu hv, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_mul {Λ K R : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    (e : K →ₐ[Λ] R) (J : Ideal K) (Q P : Submodule Λ R) (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x)
    (hP : ∀ x ∈ P, ∃ y, e y = x) : ∀ x ∈ Q * P, ∃ y ∈ J, e y = x := by
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hQ a ha
    obtain ⟨v, rfl⟩ := hP b hb
    exact ⟨u * v, J.mul_mem_right v hu, map_mul e u v⟩
  · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    exact ⟨u + v, add_mem hu hv, map_add e u v⟩

private theorem UpperTheory.V.Ws.sxContGr_cont {Λ K R Γ : Type} [CommRing Λ] [CommRing K] [CommRing R] [Algebra Λ K] [Algebra Λ R]
    [TopologicalSpace Γ] (e : K →ₐ[Λ] R) (he : Function.Injective e) (I : Ideal R) (J : Ideal K) (Q P P' : Submodule Λ R)
    (hQ : ∀ x ∈ Q, ∃ y ∈ J, e y = x) (hP : ∀ x ∈ P, ∃ y, e y = x) (hP' : ∀ x ∈ P', ∃ y, e y = x)
    (h : ∀ n : ℕ, ∃ M : ℕ, P' ⊓ (I ^ M).restrictScalars Λ ≤ Q ^ n * P * P')
    (φ : Γ → K) (hφ : ∀ g, e (φ g) ∈ P') (hc : AdicCont I fun g => e (φ g)) : AdicCont J φ := by
  intro N
  obtain ⟨M, hM⟩ := h N
  have key : ∀ x ∈ Q ^ N * P * P', ∃ y ∈ J ^ N, e y = x := by
    intro x hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := UpperTheory.V.Ws.sxContGr_mul e (J ^ N) (Q ^ N) P
        (UpperTheory.V.Ws.sxContGr_pow e J Q hQ N) hP a ha
      obtain ⟨v, rfl⟩ := hP' b hb
      exact ⟨u * v, (J ^ N).mul_mem_right v hu, map_mul e u v⟩
    · rintro a b ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
      exact ⟨u + v, add_mem hu hv, map_add e u v⟩
  have hcM : IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ M)) (e (φ g)) := hc M
  refine (IsLocallyConstant.iff_exists_open _).2 fun g0 => ?_
  refine ⟨{g | (Ideal.Quotient.mk (I ^ M)) (e (φ g)) = (Ideal.Quotient.mk (I ^ M)) (e (φ g0))},
    hcM.isOpen_fiber _, rfl, fun g hg => ?_⟩
  have hd : e (φ g) - e (φ g0) ∈ I ^ M := Ideal.Quotient.eq.1 hg
  have hd' : e (φ g) - e (φ g0) ∈ P' ⊓ (I ^ M).restrictScalars Λ :=
    Submodule.mem_inf.2 ⟨sub_mem (hφ g) (hφ g0), (Submodule.restrictScalars_mem _ _ _).2 hd⟩
  obtain ⟨y, hy, hye⟩ := key _ (hM hd')
  rw [← map_sub] at hye
  have : y = φ g - φ g0 := he hye
  exact Ideal.Quotient.eq.2 (this ▸ hy)

theorem UpperTheory.V.Ws.sxContGr :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO Λ (W.gr 0)] {Γ : Type} [TopologicalSpace Γ], (∀ (j : X) (φ : Γ → W.A), (∀ g, φ g ∈ W.gr j) → AdicCont (maximalIdeal R) (fun g => (φ g : R)) → AdicCont ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A)) φ) ∧ ∀ φ : Γ → W.gr 0, AdicCont (maximalIdeal R) (fun g => ((φ g : W.A) : R)) → AdicCont (maximalIdeal (W.gr 0)) φ := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz _ Γ _
  obtain ⟨hmax, -⟩ := wPres_maximalIdeal_gr_zero_eq_sup_span_monomials Λ X R W hz
  have hfilt := part_filt Λ X R W hz
  have hb : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have ha : ∀ a : Λ, ((algebraMap Λ (W.gr 0) a : W.A) : R) = algebraMap Λ R a :=
    fun a => by first | rfl | simp
  refine ⟨fun j φ hφ hc => ?_, fun φ hc => ?_⟩
  · refine UpperTheory.V.Ws.sxContGr_cont W.A.val Subtype.val_injective (maximalIdeal R)
      ((maximalIdeal (W.gr 0)).map (algebraMap (W.gr 0) W.A))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part j) ?_ ?_ ?_
      (fun n => hfilt j n) φ (fun g => hφ g) hc
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      refine ⟨algebraMap (W.gr 0) W.A ⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        Ideal.mem_map_of_mem _ ((hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm)), ?_⟩
      rw [hb]
      rfl
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    · exact fun x hx => ⟨⟨x, W.part_le_A hx⟩, rfl⟩
  · let e : W.gr 0 →ₐ[Λ] R := AlgHom.mk ((W.A.val : W.A →+* R).comp (algebraMap (W.gr 0) W.A))
      (fun a => by
        show W.A.val (algebraMap (W.gr 0) W.A (algebraMap Λ (W.gr 0) a)) = _
        rw [hb]
        exact ha a)
    have he : ∀ b : W.gr 0, e b = ((b : W.A) : R) := fun b => by
      show W.A.val (algebraMap (W.gr 0) W.A b) = _
      rw [hb]
      rfl
    have hinj : Function.Injective e := by
      intro b c hbc
      rw [he, he] at hbc
      exact Subtype.ext (Subtype.ext hbc)
    have hc' : AdicCont (maximalIdeal R) fun g => e (φ g) := by
      have hfun : (fun g => e (φ g)) = fun g => ((φ g : W.A) : R) := funext fun g => he _
      rw [hfun]
      exact hc
    refine UpperTheory.V.Ws.sxContGr_cont e hinj (maximalIdeal R) (maximalIdeal (W.gr 0))
      (W.part 0 ⊓ (maximalIdeal R).restrictScalars Λ) (W.part 0) (W.part 0) ?_ ?_ ?_
      (fun n => hfilt 0 n) φ (fun g => by rw [he]; exact (φ g).2) hc'
    · intro x hx
      obtain ⟨hx0, hxm⟩ := Submodule.mem_inf.1 hx
      exact ⟨⟨⟨x, W.part_le_A hx0⟩, hx0⟩,
        (hmax _).2 ((Submodule.restrictScalars_mem _ _ _).1 hxm), he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
    · exact fun x hx => ⟨⟨⟨x, W.part_le_A hx⟩, hx⟩, he _⟩
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLaurDesc :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {X : Type} [AddCommGroup X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] (W : WPres Λ X R) {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y) → ∃ f : W.A →ₐ[Λ] R', ∀ j, ∀ x ∈ W.gr j, e (F x) = HahnSeries.single (τ j) (f x) := by
  intro Λ _ _ X _ _ R _ _ W R' _ _ _ S _ _ _ c e hL τ F hF
  let φ : ∀ j, W.gr j →ₗ[Λ] R' := fun j =>
    { toFun := fun x => (e (F ((x : W.A) : R))).coeff (τ j)
      map_add' := fun x y => by
        simp only [Submodule.coe_add, Subalgebra.coe_add, map_add (f := _), HahnSeries.coeff_add]
      map_smul' := fun a x => by
        have h1 : (((a • x : W.gr j) : W.A) : R) = algebraMap Λ R a * ((x : W.A) : R) := by
          rw [← Algebra.smul_def]; rfl
        rw [h1, map_mul, AlgHom.commutes, map_mul, hL.alg, HahnSeries.coeff_single_zero_mul,
          RingHom.id_apply, Algebra.smul_def] }
  have key : ∀ j (x : W.gr j), e (F ((x : W.A) : R)) = HahnSeries.single (τ j) (φ j x) := by
    intro j x
    obtain ⟨y, hy⟩ := hF j ((x : W.A) : R) x.2
    have h2 : φ j x = y := by
      show (e (F ((x : W.A) : R))).coeff (τ j) = y
      rw [hy, HahnSeries.coeff_single_same]
    rw [h2, hy]
  have hone : φ 0 (GradedMonoid.GOne.one (A := fun j => W.gr j)) = 1 := by
    show (e (F 1)).coeff (τ 0) = 1
    rw [map_one, map_one, map_zero, HahnSeries.coeff_one, if_pos rfl]
  have hmul : ∀ {i j} (a : W.gr i) (b : W.gr j), φ _ (GradedMonoid.GMul.mul (A := fun j => W.gr j) a b) = φ i a * φ j b := by
    intro i j a b
    show (e (F (((a : W.A) : R) * ((b : W.A) : R)))).coeff (τ (i + j)) = _
    rw [map_mul, map_mul, key, key, HahnSeries.single_mul_single, map_add (f := _), HahnSeries.coeff_single_same]
  refine ⟨(DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
    (DirectSum.decomposeAlgEquiv W.gr).toAlgHom, fun j x hx => ?_⟩
  have h : DirectSum.decompose W.gr x = DirectSum.of (fun j => W.gr j) j ⟨x, hx⟩ :=
    DirectSum.decompose_of_mem W.gr hx
  have h3 : ((DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
      (DirectSum.decomposeAlgEquiv W.gr).toAlgHom) x = φ j ⟨x, hx⟩ := by
    show DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul (DirectSum.decompose W.gr x) = _
    rw [h]
    exact DirectSum.toSemiring_of (fun j => (φ j).toAddMonoidHom) hone hmul j _
  rw [h3]
  exact key j ⟨x, hx⟩
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section
variable {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

private theorem ch_adj (g : R →+* R') (X : M4 R) : adj (X.map g) = (adj X).map g := by
  ext i j
  simp [adj]

private theorem ch_map (D : RD Φ R) (f : R →+* R') (g : R' →+* R'') : (D.map f).map g = D.map (g.comp f) := by
  apply RD.ext
  · ext s i j
    rfl
  · funext v i
    ext s
    rfl

private theorem ch_conj (D : RD Φ R) (g : R →+* R') (X : M4 R) (s : Γ) (i j : Fin 4) :
    (adj (X.map g) * (D.map g).r s * X.map g) i j = g ((adj X * D.r s * X) i j) := by
  rw [ch_adj]
  show ((adj X).map g * (D.r s).map g * X.map g) i j = _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

private theorem ch_gsp (g : R →+* R') (X : M4 R) (i j : Fin 4) :
    (adj (X.map g) * X.map g - 1) i j = g ((adj X * X - 1) i j) := by
  rw [ch_adj, ← Matrix.map_mul, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub,
    Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

private def chEq (D : RD Φ R) (n : Φ.ι → M4 R) : Set R :=
  {x | (∃ v i j, x = (adj (n v) * n v - 1) i j) ∨ (∃ v i, x = n v i i - 1) ∨ (∃ v i j, i < j ∧ x = n v i j) ∨
    (∃ v, ∃ s ∈ Φ.Gv v, ∃ i j, j < i ∧ x = (adj (n v) * D.r s * n v) i j) ∨
    (∃ v i, ∃ s : Φ.Gv v, x = (adj (n v) * D.r s * n v) i i - D.ψ v i s) ∨
    ∃ v i, ∃ s : Φ.Gv v, (s : Γ) ∈ Φ.Mu v ∧ x = D.ψ v i s - 1}

private theorem ch_iff (D : RD Φ R) (n : Φ.ι → M4 R) (g : R →+* R') :
    (D.map g).Flags (fun v => (n v).map g) ↔ ∀ x ∈ chEq D n, g x = 0 := by
  constructor
  · rintro ⟨hlow, hflag, hchar, hmu⟩ x hx
    rcases hx with ⟨v, i, j, rfl⟩ | ⟨v, i, rfl⟩ | ⟨v, i, j, hij, rfl⟩ | ⟨v, s, hs, i, j, hij, rfl⟩ |
      ⟨v, i, s, rfl⟩ | ⟨v, i, s, hs, rfl⟩
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow IsGSp at hl
      rw [← ch_gsp, hl.1]
      simp
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      rw [map_sub, map_one, sub_eq_zero]
      exact hl.2.1 i
    · have hl : IsLow ((n v).map g) := hlow v
      unfold IsLow at hl
      exact hl.2.2 i j hij
    · rw [← ch_conj]
      exact hflag v s hs i j hij
    · rw [map_sub, sub_eq_zero, ← ch_conj]
      exact hchar v i s
    · rw [map_sub, map_one, sub_eq_zero]
      exact hmu v i s hs
  · intro h
    refine ⟨fun v => ?_, fun v s hs i j hij => ?_, fun v i s => ?_, fun v i s hs => ?_⟩
    · unfold IsLow IsGSp
      refine ⟨?_, fun i => ?_, fun i j hij => ?_⟩
      · ext i j
        have hx := h _ (Or.inl ⟨v, i, j, rfl⟩)
        rw [← ch_gsp, Matrix.sub_apply, sub_eq_zero] at hx
        rw [one_smul]
        exact hx
      · have hx := h _ (Or.inr (Or.inl ⟨v, i, rfl⟩))
        rw [map_sub, map_one, sub_eq_zero] at hx
        exact hx
      · exact h _ (Or.inr (Or.inr (Or.inl ⟨v, i, j, hij, rfl⟩)))
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, s, hs, i, j, hij, rfl⟩))))
      rw [← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨v, i, s, rfl⟩)))))
      rw [map_sub, sub_eq_zero, ← ch_conj] at hx
      exact hx
    · have hx := h _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, i, s, hs, rfl⟩)))))
      rw [map_sub, map_one, sub_eq_zero] at hx
      exact hx

end

theorem UpperTheory.V.Ws.sxChart :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {A₀ : Type} [CommRing A₀] (D : RD Φ A₀), ∃ (A : Type) (_ : CommRing A) (_ : Algebra A₀ A) (n : Φ.ι → M4 A), Algebra.FiniteType A₀ A ∧ Algebra.adjoin A₀ (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) = ⊤ ∧ (D.map (algebraMap A₀ A)).Flags n ∧ ∀ (R : Type) [CommRing R] (f : A₀ →+* R) (n' : Φ.ι → M4 R), (D.map f).Flags n' → ∃ F : A →+* R, F.comp (algebraMap A₀ A) = f ∧ ∀ v, (n v).map F = n' v := by
  intro O Γ _ _ Φ A₀ _ D
  classical
  let σ := Φ.ι × Fin 4 × Fin 4
  let N : Φ.ι → M4 (MvPolynomial σ A₀) := fun v => Matrix.of fun i j => MvPolynomial.X (v, i, j)
  let I : Ideal (MvPolynomial σ A₀) := Ideal.span (chEq (D.map MvPolynomial.C) N)
  let n : Φ.ι → M4 (MvPolynomial σ A₀ ⧸ I) := fun v => (N v).map (Ideal.Quotient.mk I)
  have hfac : algebraMap A₀ (MvPolynomial σ A₀ ⧸ I) = (Ideal.Quotient.mk I).comp MvPolynomial.C :=
    RingHom.ext fun _ => rfl
  refine ⟨MvPolynomial σ A₀ ⧸ I, inferInstance, inferInstance, n, ?_, ?_, ?_, ?_⟩
  · exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A₀ I) (Ideal.Quotient.mkₐ_surjective A₀ I)
  · have hset : (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) =
        (Ideal.Quotient.mkₐ A₀ I) '' Set.range (MvPolynomial.X : σ → MvPolynomial σ A₀) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨MvPolynomial.X x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    rw [hset, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective A₀ I
  · rw [hfac, ← ch_map]
    exact (ch_iff _ _ _).2 fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
  · intro R _ f n' hn'
    let φ : MvPolynomial σ A₀ →+* R := MvPolynomial.eval₂Hom f fun x => n' x.1 x.2.1 x.2.2
    have hφC : φ.comp MvPolynomial.C = f := MvPolynomial.eval₂Hom_comp_C f _
    have hN : ∀ v, (N v).map φ = n' v := by
      intro v
      ext i j
      simp [φ, N]
    have hfl : ((D.map MvPolynomial.C).map φ).Flags (fun v => (N v).map φ) := by
      have hfun : (fun v => (N v).map φ) = n' := funext hN
      rw [ch_map, hφC, hfun]
      exact hn'
    have hker : I ≤ RingHom.ker φ :=
      Ideal.span_le.2 fun x hx => RingHom.mem_ker.2 ((ch_iff _ _ _).1 hfl x hx)
    refine ⟨Ideal.Quotient.lift I φ fun a ha => RingHom.mem_ker.1 (hker ha), ?_, ?_⟩
    · rw [hfac, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hφC]
    · intro v
      rw [← hN v]
      ext i j
      simp [n]
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearMap :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R} (f : R →ₐ[Λ] R'), Φ.Near a τ D → Φ.Near a τ (D.map (f : R →+* R')) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ R' _ _ _ τ D f hD
  have hr : ∀ g i j, (D.map (f : R →+* R')).r g i j = f (D.r g i j) := by
    intro g i j
    simp [RD.map, mapRep]
  have hψ : ∀ v i s, (D.map (f : R →+* R')).ψ v i s = f (D.ψ v i s) := by
    intro v i s
    simp [RD.map]
  have hm : maximalIdeal R ≤ Ideal.comap (f : R →+* R') (maximalIdeal R') := by
    intro x hx
    rw [Ideal.mem_comap]
    show f x ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ R', res_map, res_eq_zero_iff]
    exact hx
  have hadj : ∀ X : M4 R, adj ((f : R →+* R').mapMatrix X) = (f : R →+* R').mapMatrix (adj X) := by
    intro X
    ext i j
    simp [adj_apply, map_zsmul]
  have hrm : ∀ g, (D.map (f : R →+* R')).r g = (f : R →+* R').mapMatrix (D.r g) := by
    intro g
    ext i j
    rw [hr]
    simp
  refine ⟨⟨fun g => ?_, fun g hg => ?_, ?_⟩, fun i j => ?_, fun v i => ?_, fun g i => ?_,
    fun g i j hij hτ => ?_, fun v i s => ?_⟩
  · have hX : adj (D.r g) * D.r g = (algebraMap Λ R) (a ↑(Φ.ν g)) • 1 := hD.rep.mult g
    have h := congrArg (f : R →+* R').mapMatrix hX
    rw [map_mul, ← hadj, ← hrm] at h
    show adj ((D.map (f : R →+* R')).r g) * (D.map (f : R →+* R')).r g =
      ((algebraMap Λ R').comp a) ↑(Φ.ν g) • 1
    rw [h]
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  · rw [hrm, hD.rep.kill g hg, map_one]
  · intro i j hij
    rw [hrm]
    simp [hD.rep.nrm hij]
  · simpa [hr] using adicCont_map (f : R →+* R') hm (hD.cont i j)
  · simpa [hψ] using adicCont_map (f : R →+* R') hm (hD.contψ v i)
  · rw [hr, res_map]
    exact hD.diag g i
  · rw [hr]
    exact hm (hD.off g i j hij hτ)
  · rw [hψ, res_map]
    exact hD.redψ v i s
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def Pm {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    (w : ℤ × ℤ) (x : R) : Prop := ∃ e ∈ E, ∃ m ∈ mono r w, x = e * m

private theorem Pm_mem {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] (r : Γ →* M4 R) (E : Subalgebra Λ R)
    {x : R} (hx : x ∈ E) : Pm r E 0 x := ⟨x, hx, 1, ⟨[], by simp, by simp⟩, by simp⟩

private theorem Pm_mul {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w w' : ℤ × ℤ} {x y : R} (hx : Pm r E w x) (hy : Pm r E w' y) : Pm r E (w + w') (x * y) := by
  obtain ⟨e, he, m, ⟨L, hL, rfl⟩, rfl⟩ := hx
  obtain ⟨e', he', m', ⟨L', hL', rfl⟩, rfl⟩ := hy
  refine ⟨e * e', mul_mem he he', _, ⟨L ++ L', by rw [List.map_append, List.sum_append, hL, hL'], rfl⟩, ?_⟩
  rw [List.map_append, List.prod_append]
  ring

private theorem Pm_pow {Λ R Γ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group Γ] {r : Γ →* M4 R} {E : Subalgebra Λ R}
    {w : ℤ × ℤ} {x : R} (hx : Pm r E w x) (k : ℕ) : Pm r E (k • w) (x ^ k) := by
  induction k with
  | zero => rw [zero_smul, pow_zero]; exact Pm_mem r E (one_mem E)
  | succ k ih => rw [succ_nsmul, pow_succ]; exact Pm_mul ih hx

theorem UpperTheory.V.Ws.sxZMono :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R} (E : Subalgebra Λ R), RD.Graded D W → mono D.r 0 ⊆ E → (∀ v i s, D.ψ v i s ∈ E) → ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ E := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W E hG hm hψ n hn
  have hz : ∀ s, Pm D.r E (W.wt s) (W.z s) := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, h1, h2, h3⟩ | ⟨v, i, t, c, h1, h2⟩
    · have hmem : D.r g i j ∈ mono D.r (wt i j) := ⟨[(g, i, j)], by simp, by simp⟩
      by_cases hij : i = j
      · have h0 : wt i j = 0 := (wt_eq_zero i j).2 hij
        rw [h2, h1, h0]
        rw [h0] at hmem
        exact Pm_mem _ _ (sub_mem (hm hmem) (E.algebraMap_mem c))
      · rw [h2, h1, h3 hij, map_zero, sub_zero]
        exact ⟨1, one_mem E, _, hmem, (one_mul _).symm⟩
    · rw [h2, h1]
      exact Pm_mem _ _ (sub_mem (hψ v i t) (E.algebraMap_mem c))
  have key : ∀ n : W.σ →₀ ℕ, Pm D.r E (Finsupp.weight W.wt n) (n.prod fun s k => W.z s ^ k) := by
    intro n
    induction n using Finsupp.induction_linear with
    | zero => rw [map_zero, Finsupp.prod_zero_index]; exact Pm_mem _ _ (one_mem E)
    | add f g hf hg =>
      rw [map_add (f := _), Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      exact Pm_mul hf hg
    | single s k =>
      rw [Finsupp.prod_single_index (h := fun s k => W.z s ^ k) (pow_zero _), Finsupp.weight_single]
      exact Pm_pow (hz s) k
  obtain ⟨e, he, m, hm', h⟩ := key n
  rw [h]
  rw [hn] at hm'
  exact mul_mem he (hm hm')
end
