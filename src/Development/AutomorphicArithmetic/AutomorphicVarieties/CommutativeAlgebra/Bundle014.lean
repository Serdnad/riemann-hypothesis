module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
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
public import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem pres_new_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R) :
    F g - F (truncTotal n g : MvPolynomial σ R) ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have h := key (e (g - (truncTotal n g : MvPolynomial σ R))) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n (g - ((truncTotal n g : MvPolynomial σ R) : MvPowerSeries σ R)) = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply, map_sub] at h

private theorem pres_new_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (N : ℕ) :
    ∀ h ∈ maximalIdeal (MvPowerSeries σ O) ^ N, ∀ a : σ →₀ ℕ,
      coeff a h ∈ maximalIdeal O ^ (N - a.degree) :=
  _root_.UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff N

private theorem pres_new_wcomp {O σ X : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] (wt : σ → X)
    {i : X} (j : X) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt i) :
    wcomp O wt j h = if i = j then h else 0 := by
  ext a
  rw [coeff_wcomp]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    split_ifs with h1
    · rfl
    · exact (hh a h1).symm
  · rw [if_neg hij]
    split_ifs with h1
    · rw [map_zero]
      exact hh a (h1 ▸ Ne.symm hij)
    · simp

private theorem pres_new_mono {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (u : τ →₀ ℕ) : Φ (monomial u 1) ∈ wtPart O w (Finsupp.weight wt u) := by
  induction u using Finsupp.induction_linear with
  | zero => simpa using one_mem_wtPart O w
  | add u v hu hv =>
    have : (monomial (u + v) 1 : MvPowerSeries τ O) = monomial u 1 * monomial v 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_mul, map_add (f := _)]
    exact mul_mem_wtPart O w hu hv
  | single s n =>
    rw [← X_pow_eq, map_pow, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hΦ s)

private theorem pres_new_poly {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s)) (j : Y)
    (p : MvPolynomial τ O) : Φ (wcomp O wt j p) = wcomp O w j (Φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    have : ((MvPolynomial.monomial u c : MvPolynomial τ O) : MvPowerSeries τ O) = c • monomial u 1 := by
      rw [MvPolynomial.coe_monomial, ← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, map_smul, pres_new_wcomp w j (pres_new_mono wt w Φ hΦ u),
      pres_new_wcomp wt j (h := monomial u 1) (pres_new_mono wt wt (AlgHom.id O _) (X_mem_wtPart O wt) u)]
    split_ifs <;> simp
  | add p q hp hq => simp only [MvPolynomial.coe_add, map_add (f := _), hp, hq]

private theorem pres_new_comm {O σ τ Y : Type} [CommRing O] [IsLocalRing O] [IsHausdorff (maximalIdeal O) O]
    [Finite τ] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (hm : ∀ s, Φ (X s) ∈ maximalIdeal (MvPowerSeries σ O)) (j : Y)
    (g : MvPowerSeries τ O) : Φ (wcomp O wt j g) = wcomp O w j (Φ g) := by
  have hl := pres_new_low (maximalIdeal (MvPowerSeries σ O)) (Φ : MvPowerSeries τ O →+* MvPowerSeries σ O) hm
  ext a
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal O) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have h1 := pres_new_coeff _ _ (hl (k + a.degree) g) a
  have h2 := pres_new_coeff _ _ (hl (k + a.degree) (wcomp O wt j g)) a
  have h3 : ((truncTotal (k + a.degree) (wcomp O wt j g) : MvPolynomial τ O) : MvPowerSeries τ O) =
      wcomp O wt j (truncTotal (k + a.degree) g : MvPolynomial τ O) := by
    ext b
    simp only [coeff_wcomp, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]
    split_ifs <;> rfl
  rw [h3] at h2
  simp only [RingHom.coe_coe, Nat.add_sub_cancel, map_sub] at h1 h2
  rw [pres_new_poly wt w Φ hΦ] at h2
  rw [coeff_wcomp] at h2 ⊢
  split_ifs at h2 ⊢
  · simpa using sub_mem h2 h1
  · exact h2

theorem UpperTheory.V.Alg.pres_new :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (τ : Type) [Fintype τ] (wt : τ → X) (z : τ → R), (∀ s, z s ∈ maximalIdeal R ∧ z s ∈ W.part (wt s)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 →
      ∃ (W' : WPres O X R) (e : τ ≃ W'.σ), ∀ s, W'.z (e s) = z s ∧ W'.wt (e s) = wt s := by
  intro O _ _ _ _ Y _ _ _ _ R _ _ _ W _ τ _ wt z hz hgen
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries τ O) := co_mvps O O τ
  choose f hf hfz using fun s => (hz s).2
  have hfz' : ∀ s, W.π (f s) = z s := hfz
  have hfm : ∀ s, f s ∈ maximalIdeal (MvPowerSeries W.σ O) := fun s hu =>
    (hz s).1 (hfz' s ▸ hu.map W.π)
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := co_ev O O (MvPowerSeries W.σ O) τ (Algebra.ofId _ _) f hfm
  have hF : ∀ s, (W.π.comp Φ) (X s) = z s := fun s => by rw [AlgHom.comp_apply, hΦ, hfz']
  refine ⟨⟨τ, wt, W.π.comp Φ, ?_, ?_⟩, Equiv.refl _, fun s => ⟨hF s, rfl⟩⟩
  · refine co_surj O _ R _ (hgen.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hF s]
      refine Ideal.mem_map_of_mem _ fun hu => ?_
      simpa using isUnit_constantCoeff _ hu
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← (W.π.comp Φ).commutes]
      refine Ideal.mem_map_of_mem _ fun hu => hc ?_
      simpa [MvPowerSeries.algebraMap_apply] using isUnit_constantCoeff _ hu
  · intro g hg j
    show W.π (Φ _) = 0
    rw [pres_new_comm wt W.wt Φ (fun s => hΦ s ▸ hf s) (fun s => hΦ s ▸ hfm s)]
    exact W.homog _ hg j
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem weight_zero_power_series_surjective (O : Type) [CommRing O] {σ τ X : Type} [Finite τ] [AddCommGroup X] (wt : σ → X)
    (g : τ → (σ →₀ ℕ)) (hg0 : ∀ s, g s ≠ 0) (hgw : ∀ s, Finsupp.weight wt (g s) = 0)
    (hgen : ∀ n, Finsupp.weight wt n = 0 → ∃ d : τ →₀ ℕ, Finsupp.linearCombination ℕ g d = n) :
    ∃ φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O,
      (∀ F, φ F ∈ wtPart O wt 0) ∧ ∀ f ∈ wtPart O wt 0, ∃ F, φ F = f := by
  classical
  let a : τ → MvPowerSeries σ O := fun s => monomial (g s) 1
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero fun s => by
    show constantCoeff (monomial (g s) (1 : O)) = 0
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg (hg0 s).symm]
  have hprod : ∀ d : τ →₀ ℕ, (d.prod fun s e => a s ^ e) = monomial (Finsupp.linearCombination ℕ g d) (1 : O) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' =>
      rw [Finsupp.prod_add_index' (by simp) (fun s m n => pow_add _ _ _), h, h', map_add (f := _), monomial_mul_monomial,
        one_mul]
    | single s k =>
      rw [Finsupp.prod_single_index (by simp), Finsupp.linearCombination_single]
      show (monomial (g s) (1 : O)) ^ k = _
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ih, monomial_mul_monomial, one_mul, succ_nsmul]
  have hw : ∀ d : τ →₀ ℕ, Finsupp.weight wt (Finsupp.linearCombination ℕ g d) = 0 := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' h h' => rw [map_add (f := _), map_add (f := _), h, h', add_zero]
    | single s k => rw [Finsupp.linearCombination_single, map_nsmul, hgw, nsmul_zero]
  have hco : ∀ (F : MvPowerSeries τ O) n, coeff n (substAlgHom ha F) =
      ∑ᶠ d, coeff d F * (if n = Finsupp.linearCombination ℕ g d then 1 else 0) := by
    intro F n
    rw [coe_substAlgHom, coeff_subst ha]
    refine finsum_congr fun d => ?_
    rw [hprod, coeff_monomial, smul_eq_mul]
  refine ⟨substAlgHom ha, fun F n hn => ?_, fun f hf => ?_⟩
  · rw [hco]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (hw d)
  · choose! e he using hgen
    let F : MvPowerSeries τ O := fun d =>
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0
    have hF : ∀ d, coeff d F =
      if d = e (Finsupp.linearCombination ℕ g d) then coeff (Finsupp.linearCombination ℕ g d) f else 0 :=
      fun _ => rfl
    refine ⟨F, ?_⟩
    ext n
    rw [hco]
    by_cases hn : Finsupp.weight wt n = 0
    · rw [finsum_eq_single _ (e n)]
      · rw [hF, he n hn, if_pos rfl, if_pos rfl, mul_one]
      · intro d hd
        by_cases h : n = Finsupp.linearCombination ℕ g d
        · rw [hF, ← h, if_neg hd, zero_mul]
        · rw [if_neg h, mul_zero]
    · rw [hf n hn]
      refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
      rw [if_neg, mul_zero]
      rintro rfl
      exact hn (hw d)

theorem UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsCO O (W.gr 0) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _
  obtain ⟨g, hg, hgen, -⟩ := UpperTheory.V.Alg.gordan W.σ X W.wt
  obtain ⟨φ, hφ, hs⟩ := weight_zero_power_series_surjective O W.wt (fun s : g => (s : W.σ →₀ ℕ)) (fun s => (hg s s.2).1)
    (fun s => (hg s s.2).2) (fun n hn => by
      have h := hgen n hn
      induction h using AddSubmonoid.closure_induction with
      | mem x hx => exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp⟩
      | zero => exact ⟨0, map_zero _⟩
      | add x y hx hy ihx ihy =>
        have hw : ∀ z ∈ AddSubmonoid.closure (g : Set (W.σ →₀ ℕ)), Finsupp.weight W.wt z = 0 := by
          intro z hz
          induction hz using AddSubmonoid.closure_induction with
          | mem x hx => exact (hg x hx).2
          | zero => exact map_zero _
          | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
        obtain ⟨d, hd⟩ := ihx (hw x hx)
        obtain ⟨d', hd'⟩ := ihy (hw y hy)
        exact ⟨d + d', by rw [map_add (f := _), hd, hd']⟩)
  have hp : ∀ F, W.π (φ F) ∈ W.part 0 := fun F => ⟨φ F, hφ F, rfl⟩
  let p : MvPowerSeries g O →ₐ[O] W.gr 0 :=
    { toFun := fun F => ⟨⟨W.π (φ F), W.part_le_A (hp F)⟩, hp F⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun F G => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun F G => Subtype.ext (Subtype.ext (by simp))
      commutes' := fun c => Subtype.ext (Subtype.ext (by
        show W.π (φ (algebraMap O _ c)) = algebraMap O R c
        rw [AlgHom.commutes, AlgHom.commutes])) }
  haveI : IsCO O (MvPowerSeries g O) := UpperTheory.V.Alg.co_mvps O O g
  haveI : Nontrivial (W.gr 0) := ⟨⟨0, 1, fun h =>
    zero_ne_one (α := R) (congrArg (fun x : W.gr 0 => ((x : W.A) : R)) h)⟩⟩
  refine UpperTheory.V.Alg.co_quot O (MvPowerSeries g O) (W.gr 0) p ?_
  rintro ⟨⟨x, hxA⟩, f, hf, hx⟩
  obtain ⟨F, rfl⟩ := hs f hf
  exact ⟨F, Subtype.ext (Subtype.ext hx)⟩
end

section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem eigen_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : ∀ d : σ →₀ ℕ, d.degree < n → coeff d g = 0) : F g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n g = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [hg x hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem eigen_split {O σ X : Type} [CommRing O] [Finite σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (n : ℕ) (g : MvPowerSeries σ O) : ∃ s : Finset X, j ∈ s ∧
      ∀ d : σ →₀ ℕ, d.degree < n → coeff d (g - ∑ i ∈ s, wcomp O wt i g) = 0 := by
  classical
  refine ⟨insert j ((truncTotal n g).support.image (Finsupp.weight wt)), Finset.mem_insert_self _ _,
    fun d hd => ?_⟩

  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra hne
    refine h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_))
    rwa [MvPolynomial.mem_support_iff, coeff_truncTotal _ hd]

theorem UpperTheory.V.Alg.eigen_mem :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (x : R) (j : X),
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ i, res O R' (t i) = 1) →
        (∀ s, f' (W.z s) = t (Multiplicative.ofAdd (W.wt s)) * f (W.z s)) → f' x = t (Multiplicative.ofAdd j) * f x) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ R _ _ hR W hz x j H
  classical
  obtain ⟨n, t0, ht1, hind⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) R) := co_mvps O R (Fin n)
  let f : R →ₐ[O] MvPowerSeries (Fin n) R :=
    { (C : R →+* MvPowerSeries (Fin n) R) with commutes' := fun a => (MvPowerSeries.algebraMap_apply).symm }
  have hf : ∀ a, f a = C a := fun _ => rfl
  let t : Multiplicative X →* (MvPowerSeries (Fin n) R)ˣ :=
    (Units.map (MvPowerSeries.map (σ := Fin n) (algebraMap O R)).toMonoidHom).comp t0
  have ht : ∀ i, (t i : MvPowerSeries (Fin n) R) =
      MvPowerSeries.map (algebraMap O R) (t0 i : MvPowerSeries (Fin n) O) := fun _ => rfl
  have hres : ∀ i, res O (MvPowerSeries (Fin n) R) (t i) = 1 := fun i => by
    have h : (t i : MvPowerSeries (Fin n) R) - 1 ∈ maximalIdeal (MvPowerSeries (Fin n) R) := fun hu => by
      have h2 := isUnit_constantCoeff _ hu
      rw [map_sub, ht, constantCoeff_map, ht1, map_one, map_one, sub_self] at h2
      exact not_isUnit_zero h2
    have := (res_eq_zero_iff O _ _).2 h
    rwa [map_sub, map_one, sub_eq_zero] at this
  obtain ⟨f', hf', -⟩ := tact O X R W hz (MvPowerSeries (Fin n) R) f t
  have hx := H _ f f' t hres (fun s => hf' _ _ (W.z_mem s))
  obtain ⟨g, rfl⟩ := W.surj x
  suffices h : W.π (wcomp O W.wt j g) - W.π g = 0 by
    rw [sub_eq_zero] at h
    exact ⟨_, wcomp_mem O W.wt j g, h⟩
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨s, hjs, hs⟩ := eigen_split W.wt j N g
  have h1 := eigen_low ((maximalIdeal R).map (C : R →+* MvPowerSeries (Fin n) R))
    ((f'.comp W.π : MvPowerSeries W.σ O →ₐ[O] _) : MvPowerSeries W.σ O →+* _) (fun s => by
      show f' (W.z s) ∈ _
      rw [hf' _ _ (W.z_mem s)]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hz s))) N _ hs
  let q := Ideal.Quotient.mk (maximalIdeal R ^ N)
  have h2 : MvPowerSeries.map (σ := Fin n) q (f' (W.π (g - ∑ i ∈ s, wcomp O W.wt i g))) = 0 := by
    rw [← Ideal.map_pow] at h1
    refine (Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) : _ ≤ RingHom.ker (MvPowerSeries.map (σ := Fin n) q)) h1
    rw [Ideal.mem_comap, RingHom.mem_ker, map_C, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hq : ∀ i, MvPowerSeries.map (σ := Fin n) q (t i) =
      MvPowerSeries.map (algebraMap O (R ⧸ maximalIdeal R ^ N)) (t0 i : MvPowerSeries (Fin n) O) := fun i => by
    ext d
    rfl
  have h3 := hind (R ⧸ maximalIdeal R ^ N) s
    (fun i => q (W.π (wcomp O W.wt i g)) - if i = j then q (W.π g) else 0) (by

      rw [map_sub, map_sub, hx, map_sum, map_sum, Finset.sum_congr rfl
      (fun i _ => hf' i (W.π (wcomp O W.wt i g)) ⟨_, wcomp_mem O W.wt i g, rfl⟩), map_sub, map_sum] at h2
      simp only [map_mul, hq, hf, map_C] at h2
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib, apply_ite C, map_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', if_pos hjs]
      rw [← neg_eq_zero, neg_sub]
      exact h2) j hjs
  simp only [if_true] at h3
  rwa [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h3
end
