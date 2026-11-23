module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle047
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicMat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wt_add' (i j k : Fin 4) : wt i j + wt j k = wt i k := by
  simp [wt]

private theorem laurent_mul_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X Y : M4 S) (X0 Y0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j))
    (hY : ∀ i j, e (Y i j) = HahnSeries.single (τ (wt i j)) (Y0 i j)) (i j : Fin 4) :
    e ((X * Y) i j) = HahnSeries.single (τ (wt i j)) ((X0 * Y0) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [map_add e, map_mul, hX, hY, HahnSeries.single_mul_single, ← map_add τ, wt_add',
    HahnSeries.single_add]

private theorem laurent_adj_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X : M4 S) (X0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j)) (i j : Fin 4) :
    e ((adj X) i j) = HahnSeries.single (τ (wt i j)) ((adj X0) i j) := by
  have hrev : ∀ i j : Fin 4, wt j.rev i.rev = wt i j := by decide
  simp only [adj, Matrix.of_apply, zsmul_eq_mul, map_mul, map_intCast, hX, hrev]
  rw [← map_intCast (HahnSeries.C : R →+* LaurentSeries R), HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add]

private theorem laurent_smul_one_apply_eq_single_of_eq_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (ν : S) (ν0 : R) (hν : e ν = HahnSeries.single 0 ν0) (i j : Fin 4) :
    e ((ν • (1 : M4 S)) i j) = HahnSeries.single (τ (wt i j)) ((ν0 • (1 : M4 R)) i j) := by
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, hν, hw0]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h]

theorem UpperTheory.V.Ws.sxScaleRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R} {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R}, IsNilpotent (maximalIdeal R) → Laur (Λ := Λ) c e → (∀ i j, -(c : ℤ) ≤ τ (wt i j)) → Φ.Near a τ D → ∃ D' : RD Φ S, Φ.Near a 0 D' ∧ (∀ g i j, e (D'.r g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j)) ∧ ∀ v i s, e (D'.ψ v i s) = HahnSeries.single 0 (D.ψ v i s) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ S _ _ _ c e τ D hnil hL hc hN
  classical
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  have hresm : ∀ {T : Type} [CommRing T] [Algebra Λ T] [IsCO Λ T] (y : T), y ∈ maximalIdeal T →
      res Λ T y = 0 := by
    intro T _ _ _ y hy
    simp [res, (IsLocalRing.residue_eq_zero_iff y).mpr hy]
  have hex0 : ∀ x : R, ∃ y : S, e y = HahnSeries.single 0 x ∧ res Λ S y = res Λ R x := by
    intro x
    obtain ⟨l, hl⟩ := IsCO.res_surj (O := Λ) x
    obtain ⟨y, hy, hye⟩ := hL.mem 0 _ (Or.inr ⟨by omega, hl⟩)
    refine ⟨y + algebraMap Λ S l, ?_, ?_⟩
    · rw [map_add (f := _), hye, hL.alg, ← HahnSeries.single_add, sub_add_cancel]
    · rw [map_add (f := _), hresm y hy, AlgHom.commutes, zero_add]
      conv_rhs => rw [← sub_add_cancel x (algebraMap Λ R l)]
      rw [map_add (f := _), hresm _ hl, AlgHom.commutes, zero_add]
  have hent : ∀ g i j, ∃ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) := by
    intro g i j
    rcases lt_trichotomy (τ (wt i j)) 0 with h | h | h
    · have hij : i ≠ j := by
        rintro rfl
        rw [hw0, map_zero] at h
        exact lt_irrefl _ h
      obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h.le⟩)
      exact ⟨y, hy⟩
    · rw [h]
      obtain ⟨y, hy, -⟩ := hex0 (D.r g i j)
      exact ⟨y, hy⟩
    · obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inl h)
      exact ⟨y, hy⟩
  have hmem : ∀ g i j, i ≠ j → ∀ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) →
      y ∈ maximalIdeal S := by
    intro g i j hij y hy
    rcases le_or_gt (τ (wt i j)) 0 with h | h
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h⟩)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inl h)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
  let pre : LaurentSeries R → S := fun z => if h : ∃ y, e y = z then h.choose else 0
  have hpre : ∀ z, (∃ y, e y = z) → e (pre z) = z := by
    intro z h
    simp only [pre, dif_pos h]
    exact h.choose_spec
  have hpre0 : ∀ x : R, e (pre (HahnSeries.single 0 x)) = HahnSeries.single 0 x := by
    intro x
    obtain ⟨y, hy, -⟩ := hex0 x
    exact hpre _ ⟨y, hy⟩
  have hres0 : ∀ x : R, res Λ S (pre (HahnSeries.single 0 x)) = res Λ R x := by
    intro x
    obtain ⟨y, hy, hr⟩ := hex0 x
    rw [hL.inj ((hpre0 x).trans hy.symm)]
    exact hr
  let rr : Γ → M4 S := fun g => Matrix.of fun i j => pre (HahnSeries.single (τ (wt i j)) (D.r g i j))
  have hrr : ∀ g i j, e (rr g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) :=
    fun g i j => hpre _ (hent g i j)
  have hext : ∀ X Y : M4 S, (∀ i j, e (X i j) = e (Y i j)) → X = Y :=
    fun X Y h => Matrix.ext fun i j => hL.inj (h i j)
  have h1 : ∀ i j, e ((1 : M4 S) i j) = HahnSeries.single (τ (wt i j)) ((1 : M4 R) i j) := by
    intro i j
    have := laurent_smul_one_apply_eq_single_of_eq_single e τ 1 1 (by rw [map_one, HahnSeries.single_zero_one]) i j
    simpa only [one_smul] using this
  let r' : Γ →* M4 S :=
    { toFun := rr
      map_one' := hext _ _ fun i j => by rw [hrr, D.r.map_one, h1]
      map_mul' := fun g h => hext _ _ fun i j => by
        rw [hrr, D.r.map_mul, laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (hrr g) (hrr h)] }
  have hr' : ∀ g i j, e (r' g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) := hrr
  let ψ' : (v : Φ.ι) → Fin 4 → ↥(Φ.Gv v) →* S := fun v i =>
    { toFun := fun s => pre (HahnSeries.single 0 (D.ψ v i s))
      map_one' := hL.inj (by rw [hpre0, (D.ψ v i).map_one, HahnSeries.single_zero_one, map_one])
      map_mul' := fun s t => hL.inj (by
        rw [hpre0, (D.ψ v i).map_mul, map_mul e, hpre0, hpre0, HahnSeries.single_mul_single, zero_add]) }
  obtain ⟨K, hK⟩ := hnil
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal R ^ K)) := by
    intro x y h
    rwa [Ideal.Quotient.eq, hK, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at h
  refine ⟨⟨r', ψ'⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hr', fun v i s => hpre0 _⟩
  · intro g
    have hg : adj (D.r g) * D.r g = _ := hN.rep.mult g
    show adj (r' g) * r' g = _
    simp only [RingHom.comp_apply] at hg ⊢
    refine hext _ _ fun i j => ?_
    rw [laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (laurent_adj_apply_eq_single_of_entries_single e τ _ _ (hr' g)) (hr' g), hg,
      laurent_smul_one_apply_eq_single_of_eq_single e τ _ _ (hL.alg _)]
  · intro g hg
    refine hext _ _ fun i j => ?_
    rw [hr', hN.rep.kill g hg, h1]
  · intro i j hij
    apply hL.inj
    rw [hr', hN.rep.nrm hij, HahnSeries.single_eq_zero, map_zero]
  · intro i j N
    have h2 : IsLocallyConstant fun g => D.r g i j :=
      IsLocallyConstant.desc _ _ (hN.cont i j K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single (τ (wt i j)) x)))
  · intro v i N
    have h2 : IsLocallyConstant fun s => D.ψ v i s :=
      IsLocallyConstant.desc _ _ (hN.contψ v i K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single 0 x)))
  · intro g i
    rw [← hN.diag g i]
    show res Λ S (pre (HahnSeries.single (τ (wt i i)) (D.r g i i))) = _
    rw [hw0, map_zero]
    exact hres0 _
  · intro g i j hij _
    exact hmem g i j hij _ (hr' g i j)
  · intro v i s
    rw [← hN.redψ v i s]
    exact hres0 _
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxSubRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {Λ R : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] (a : O →+* Λ) (A : Subalgebra Λ R) (D : RD Φ R), (∀ g i j, D.r g i j ∈ A) → (∀ v i s, D.ψ v i s ∈ A) → Φ.IsRep ((algebraMap Λ R).comp a) D.r → ∃ D' : RD Φ A, D'.map (A.val : A →+* R) = D ∧ Φ.IsRep ((algebraMap Λ A).comp a) D'.r := by
  intro O Γ _ _ Φ Λ R _ _ _ a A D hr hψ h
  have h1 : ∀ i j : Fin 4, (((1 : M4 A) i j : A) : R) = (1 : M4 R) i j := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  let r' : Γ →* M4 A :=
    { toFun := fun g => Matrix.of fun i j => ⟨D.r g i j, hr g i j⟩
      map_one' := by
        ext i j
        rw [h1]; simp
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  have hr' : ∀ g i j, ((r' g i j : A) : R) = D.r g i j := fun _ _ _ => rfl
  refine ⟨⟨r', fun v i => (D.ψ v i).codRestrict A (hψ v i)⟩, ?_, fun g => ?_, fun g hg => ?_, fun i j hij => ?_⟩
  · refine RD.ext ?_ ?_
    · ext g i j; rfl
    · funext v i; ext s; rfl
  · have := h.mult g
    unfold IsGSp at this ⊢
    ext i j
    have e := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul, MulMemClass.coe_mul, h1]
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    refine Eq.trans ?_ e
    simp [Matrix.mul_apply, adj, hr']
  · ext i j
    rw [h1]
    show D.r g i j = _
    rw [h.kill g hg]
  · exact Subtype.ext (h.nrm hij)
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem laurPart_prod {S R' ι : Type} [CommRing S] [CommRing R'] (e : S →+* LaurentSeries R')
    (w : ι → ℤ) (z : ι → S) (h : ∀ s, ∃ y, e (z s) = HahnSeries.single (w s) y) (d : ι → ℕ) (t : Finset ι) :
    ∃ y, e (∏ i ∈ t, z i ^ d i) = HahnSeries.single (∑ i ∈ t, d i • w i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a t ha ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨u, hu⟩ := h a
    refine ⟨u ^ d a * y, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow, hy, hu, HahnSeries.single_pow,
      HahnSeries.single_mul_single]

theorem UpperTheory.V.Ws.sxLaurPart :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y) → ∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ S _ _ _ c e hL τ F hF j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (F.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal S := fun s => by
    show F (W.z s) ∈ maximalIdeal S
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hW s
  refine ⟨(e (F (W.π g))).coeff (τ j), ?_⟩
  ext n
  show (e (F (W.π g))).coeff n = _
  by_cases hn : n = τ j
  · subst hn
    rw [HahnSeries.coeff_single_same]
  rw [HahnSeries.coeff_single_of_ne hn]
  obtain ⟨M, hM⟩ := hL.small n
  have h1 := hM _ (GlobalTheory.algHom_sub_aeval_truncTotal_mem (F.comp W.π) hm M g)
  rw [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1
  refine h1.trans ?_

  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hg d hne, ite_self]
  obtain ⟨y, hy⟩ := laurPart_prod e (fun s => τ (W.wt s)) (fun s => F (W.z s)) hF d d.support
  have hs : (∑ i ∈ d.support, d i • τ (W.wt i)) = τ j := by

    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hs] at hy
  rw [map_mul, hL.alg]
  erw [hy]
  rw [HahnSeries.single_mul_single, zero_add, HahnSeries.coeff_single_of_ne hn]
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxCoreGen :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) = ⊤ := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ R _ _ _ D W hD D' hmap
  have hr : ∀ g i j, D.r g i j = (D'.r g i j : R) := by
    subst hmap
    intro g i j
    first | rfl | simp [RD.map]
  have hψ : ∀ v i t, D.ψ v i t = (D'.ψ v i t : R) := by
    subst hmap
    intro v i t
    first | rfl | simp [RD.map]
  set S := Algebra.adjoin (W.gr 0) (Set.range fun x : Γ × Fin 4 × Fin 4 => D'.r x.1 x.2.1 x.2.2) with hS
  have hbA : ∀ b : W.gr 0, algebraMap (W.gr 0) W.A b = (b : W.A) := fun b => by first | rfl | simp
  have hgr : ∀ x : W.A, (x : R) ∈ W.part 0 → x ∈ S := by
    intro x hx
    have h := Subalgebra.algebraMap_mem S (⟨x, hx⟩ : W.gr 0)
    rwa [hbA] at h
  have hc : ∀ c : Λ, algebraMap Λ W.A c ∈ S := by
    intro c
    apply hgr
    have h0 : algebraMap Λ R c ∈ W.part 0 := by
      have := (algebraMap Λ (W.gr 0) c).2
      first
        | exact this
        | (have e : ((algebraMap Λ (W.gr 0) c : W.A) : R) = algebraMap Λ R c := by first | rfl | simp
           rw [← e]; exact this)
    first | exact h0 | simpa using h0
  have hr' : ∀ g i j, D'.r g i j ∈ S := fun g i j => Algebra.subset_adjoin ⟨(g, i, j), rfl⟩
  have hz : ∀ s, W.zA s ∈ S := by
    intro s
    rcases hD.var s with ⟨g, i, j, c, hzs, -, -⟩ | ⟨v, i, t, c, hzs, -⟩
    · have e : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hr]
        rfl
      rw [e]
      exact sub_mem (hr' g i j) (hc c)
    · have e : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        show W.z s = _
        rw [hzs, hψ]
        rfl
      rw [e]
      refine sub_mem (hgr _ ?_) (hc c)
      rw [← hψ]
      exact hD.chr v i t
  rw [eq_top_iff]
  intro a ha0
  clear ha0
  have ha : a ∈ Algebra.adjoin Λ (↑(W.gr 0) ∪ Set.range W.zA) := by
    rw [gr_gen Λ R (ℤ × ℤ) W]
    trivial
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨s, rfl⟩
    · exact hgr x hx
    · exact hz s
  | algebraMap c => exact hc c
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem adjoin_top_of_tower {B B' A : Type} [CommRing B] [CommRing B'] [CommRing A] [Algebra B A] [Algebra B B']
    [Algebra B' A] [IsScalarTower B B' A] {s : Set A} (h : Algebra.adjoin B s = ⊤) : Algebra.adjoin B' s = ⊤ := by
  have h1 : Algebra.adjoin B s ≤ (Algebra.adjoin B' s).restrictScalars B :=
    Algebra.adjoin_le fun x hx => (Subalgebra.mem_restrictScalars B).2 (Algebra.subset_adjoin hx)
  rw [h] at h1
  exact eq_top_iff.2 fun x _ => (Subalgebra.mem_restrictScalars B).1 (h1 Algebra.mem_top)

private theorem pre_of_surj {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a) [Nontrivial Y.A] (B' : Type) [CommRing B'] [Algebra Λ B']
    (p : Y.B →ₐ[Λ] B') (hp : Function.Surjective p) (j : B' →+* Y.A) (hj : ∀ b, j (p b) = algebraMap Y.B Y.A b)
    (hi : Function.Injective j) : ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  have hp' : Function.Surjective (p : Y.B →+* B') := hp
  haveI : Nontrivial B' := j.domain_nontrivial
  haveI : IsCO Λ B' := co_quot Λ Y.B B' p hp
  letI : Algebra B' Y.A := j.toAlgebra
  letI : Algebra Y.B B' := (p : Y.B →+* B').toAlgebra
  haveI t1 : IsScalarTower Y.B B' Y.A := IsScalarTower.of_algebraMap_eq fun b => (hj b).symm
  haveI t2 : IsScalarTower Λ B' Y.A := IsScalarTower.of_algebraMap_eq fun b => by
    rw [← p.commutes, IsScalarTower.algebraMap_apply Λ Y.B Y.A]
    exact (hj _).symm
  have hm : (maximalIdeal Y.B).map (p : Y.B →+* B') = maximalIdeal B' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hle : maximalIdeal Y.B ≤ (maximalIdeal B').comap (p : Y.B →+* B') := by
    rw [← hm]; exact Ideal.le_comap_map
  have hc : (algebraMap B' Y.A).comp (p : Y.B →+* B') = algebraMap Y.B Y.A := RingHom.ext hj
  have hr : (res Λ B' : B' →+* ResidueField Λ).comp (p : Y.B →+* B') =
      (res Λ Y.B : Y.B →+* ResidueField Λ) := RingHom.ext fun b => res_map (O := Λ) (R := Y.B) p b
  haveI := Y.ft
  refine ⟨{ A := Y.A, B := B', ft := Algebra.FiniteType.of_restrictScalars_finiteType Y.B _ _
            P := Y.P, pair := Y.pair, cont := ?_, gen := adjoin_top_of_tower Y.gen
            cp := fun g => (Y.cp g).map (p : Y.B →+* B')
            cp_map := fun g => ?_, cp_cont := fun n => ?_, cp_red := fun g => ?_
            ψ := fun v i s => p (Y.ψ v i s)
            ψ_map := fun v i s hs => (hj _).trans (Y.ψ_map v i s hs)
            ψ_cont := fun v i => adicCont_map (p : Y.B →+* B') hle (Y.ψ_cont v i)
            ψ_red := fun v i s hs => (res_map (O := Λ) (R := Y.B) p _).trans (Y.ψ_red v i s hs)
            genB := fun R _ _ _ f f' h1 h2 => ?_
            univ := Y.univ }, hi⟩
  · rw [← hm, Ideal.map_map, hc]
    exact Y.cont
  · rw [Polynomial.map_map, hc, Y.cp_map]
  · simp only [coeff_map]
    exact adicCont_map (p : Y.B →+* B') hle (Y.cp_cont n)
  · rw [Polynomial.map_map, hr, Y.cp_red]
  · have h : f.comp p = f'.comp p := Y.genB R _ _ (fun g n => by
      have h3 := h1 g n
      rw [coeff_map] at h3
      exact h3) h2
    refine AlgHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := hp x
    exact AlgHom.congr_fun h b

theorem UpperTheory.V.Ws.sxPreImage :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Nontrivial Y.A → ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  intro O Γ _ _ _ Φ Λ _ _ a Y hA
  exact pre_of_surj Y (Y.B ⧸ RingHom.ker (algebraMap Y.B Y.A)) (Ideal.Quotient.mkₐ Λ _) Ideal.Quotient.mk_surjective
    (RingHom.kerLift (algebraMap Y.B Y.A)) (fun b => RingHom.kerLift_mk _ b) (RingHom.kerLift_injective _)
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_diag_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i :=
  _root_.UpperTheory.Reformulated.B.Qe40.up_diag_mul hX hY i

private theorem low_inv {R : Type} [CommRing R] {n : M4 R} (h : IsLow n) : adj n * n = 1 ∧ n * adj n = 1 := by
  have h1 : adj n * n = 1 := by
    have := h.1
    rwa [IsGSp, one_smul] at this
  exact ⟨h1, mul_eq_one_comm.1 h1⟩

private def grChar {O Γ : Type} [CommRing O] [Group Γ] {Φ : Fr O Γ} {R : Type} [CommRing R] {a : O →+* R}
    (Q : PD Φ.ι Γ R) (h : Φ.IsPair a Q) (v : Φ.ι) (i : Fin 4) : Φ.Gv v →* R where
  toFun s := Q.ψ v i s
  map_one' := by
    show (adj (Q.n v) * Q.r 1 * Q.n v) i i = 1
    rw [map_one, mul_one, (low_inv (h.low v)).1, Matrix.one_apply_eq]
  map_mul' s t := by
    show (adj (Q.n v) * Q.r (s * t) * Q.n v) i i =
      (adj (Q.n v) * Q.r s * Q.n v) i i * (adj (Q.n v) * Q.r t * Q.n v) i i
    rw [← up_diag_mul (h.flag v s s.2) (h.flag v t t.2), map_mul]
    have e : adj (Q.n v) * Q.r s * Q.n v * (adj (Q.n v) * Q.r t * Q.n v) =
        adj (Q.n v) * Q.r s * (Q.n v * adj (Q.n v)) * Q.r t * Q.n v := by simp only [mul_assoc]
    rw [e, (low_inv (h.low v)).2]
    simp only [mul_assoc, one_mul]

private def lin (p q : ℤ) : ℤ × ℤ →+ ℤ where
  toFun w := p * w.1 + q * w.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add]; ring

private theorem tau_nP : ∀ i j : Fin 4, (-2) * (wt i j).1 + (-1) * (wt i j).2 ≤ 0 → wt i j ∉ nP := by decide

private theorem tau_nM : ∀ i j : Fin 4, (-1) * (wt i j).1 + (-2) * (wt i j).2 ≤ 0 → wt i j ∉ nM := by decide

theorem UpperTheory.V.Ws.sxPairNear :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (c : PD Φ.ι Γ (ResidueField Λ)) (Q : PD Φ.ι Γ R), Φ.IsRes ((residue Λ).comp a) c → Φ.Lifts a c Q → ∃ (τ : ℤ × ℤ →+ ℤ) (D : RD Φ R), Φ.Near a τ D ∧ D.r = Q.r ∧ D.Flags Q.n := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ c Q hc hQ
  have hr : ∀ g i j, res Λ R (Q.r g i j) = c.r g i j := fun g i j => by
    rw [← hQ.red]; rfl
  have hτ : ∃ τ : ℤ × ℤ →+ ℤ, ∀ g i j, i ≠ j → τ (wt i j) ≤ 0 → c.r g i j = 0 := by
    rcases hc.res.shape with h | h
    · exact ⟨lin (-2) (-1), fun g i j hij ht => h.1 g i j hij (tau_nP i j ht)⟩
    · exact ⟨lin (-1) (-2), fun g i j hij ht => h g i j hij (tau_nM i j ht)⟩
  obtain ⟨τ, hτ⟩ := hτ
  refine ⟨τ, ⟨Q.r, grChar Q hQ.pair⟩, ⟨⟨hQ.pair.mult, hQ.pair.kill, hQ.pair.nrm⟩, hQ.cont, fun v i N => ?_,
    fun g i => ?_, fun g i j hij ht => ?_, fun v i s => ?_⟩, rfl,
    ⟨hQ.pair.low, hQ.pair.flag, fun _ _ _ => rfl, fun v i s hs => hQ.pair.mu v s hs i⟩⟩
  · exact ((sxAdicMat (maximalIdeal R) (fun g => Q.r g) hQ.cont).2 (adj (Q.n v)) (Q.n v) i i N).comp_continuous
      continuous_subtype_val
  · exact (hr g i i).trans (hc.res.diag g i)
  · exact (res_eq_zero_iff Λ R _).1 ((hr g i j).trans (hτ g i j hij ht))
  · have h1 := (sxPdMap ((algebraMap Λ R).comp a) (res Λ R : R →+* ResidueField Λ) Q).1 v i s
    rw [hQ.red] at h1
    exact h1.symm.trans (hc.res.char v s s.2 i)
end
