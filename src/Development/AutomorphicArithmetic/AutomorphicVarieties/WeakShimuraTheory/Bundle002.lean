module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.Bundle001
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg

private theorem mem_pow_iff {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    y ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) ↔ AdicCompletion.eval I A n y = 0 := by
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg]
  rfl

private theorem dense {A : Type} [CommRing A] (I : Ideal A) (fg : I.FG) (n : ℕ) (y : AdicCompletion I A) :
    ∃ z : A, y - algebraMap A (AdicCompletion I A) z ∈ (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I A n y)
  refine ⟨z, ?_⟩
  rw [mem_pow_iff I fg]
  change AdicCompletion.eval I A n (y - AdicCompletion.of I A z) = 0
  rw [map_sub, AdicCompletion.eval_of, Submodule.mkQ_apply, hz, sub_self]

private theorem lift_ex {A R : Type} [CommRing A] [CommRing R] (I : Ideal A) (J : Ideal R) [IsAdicComplete J R]
    (g : A →+* R) (hg : I ≤ J.comap g) :
    ∃ h : AdicCompletion I A →+* R, ∀ z, h (algebraMap A _ z) = g z := by
  have hle : ∀ n, I ^ n ≤ (J ^ n).comap g := fun n => (Ideal.pow_right_mono hg n).trans (Ideal.le_comap_pow _ n)
  refine ⟨IsAdicComplete.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) g (hle n)).comp (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n))
    (fun {m n} hmn => RingHom.ext fun y => ?_), fun z => ?_⟩
  · induction y using AdicCompletion.induction_on with | _ s => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk]
    exact congrArg (Ideal.quotientMap (J ^ m) g (hle m)) (AdicCompletion.Ideal.mk_eq_mk I hmn s)
  · refine IsHausdorff.eq_iff_smodEq (I := J) |>.2 fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom]
    show Ideal.quotientMap (J ^ n) g (hle n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A z)) = _
    rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem UpperTheory.V.Ws.cmplPt {Λ A : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing A] [Algebra Λ A] [IsNoetherianRing A]
    (x : A →ₐ[Λ] ResidueField Λ) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (f : A →ₐ[Λ] R),
      (f : A →+* R).Flat ∧ (res Λ R).comp f = x ∧
      ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (g : A →ₐ[Λ] R'), (res Λ R').comp g = x →
        ∃! h : R →ₐ[Λ] R', h.comp f = g := by
  have hx : ∀ z : A, ∃ c : Λ, z - algebraMap Λ A c ∈ RingHom.ker x := fun z => by
    obtain ⟨c, hc⟩ := residue_surjective (x z)
    exact ⟨c, by rw [RingHom.mem_ker, map_sub, AlgHom.commutes, ← hc]; exact sub_self _⟩
  have hs : Function.Surjective x := fun y => by
    obtain ⟨c, rfl⟩ := residue_surjective y
    exact ⟨algebraMap Λ A c, x.commutes c⟩
  set I : Ideal A := RingHom.ker x with hI
  haveI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective x hs
  have fg : I.FG := I.fg_of_isNoetherianRing
  let R := AdicCompletion I A
  haveI hmax := AdicCompletion.isMaximal_map_of_le I I le_rfl fg
  haveI hc := AdicCompletion.isAdicComplete_self I fg
  haveI : IsLocalRing R := isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap A R))
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm : maximalIdeal R = I.map (algebraMap A R) := (eq_maximalIdeal hmax).symm
  let f : A →ₐ[Λ] R := IsScalarTower.toAlgHom Λ A R
  have hf : ∀ z, f z = algebraMap A R z := fun _ => rfl
  have hIm : ∀ z ∈ I, f z ∈ maximalIdeal R := fun z hz => hm ▸ Ideal.mem_map_of_mem _ hz
  haveI hco : IsCO Λ R :=
    { complete := hm ▸ hc
      isLocalHom := ⟨fun c hu => by
        by_contra hn
        have h0 : algebraMap Λ A c ∈ I := by
          rw [RingHom.mem_ker, AlgHom.commutes]
          exact (residue_eq_zero_iff c).2 hn
        have h1 := hIm _ h0
        rw [AlgHom.commutes] at h1
        exact h1 hu⟩
      res_surj := fun y => by
        obtain ⟨z, hz⟩ := dense I fg 1 y
        obtain ⟨c, hc⟩ := hx z
        refine ⟨c, ?_⟩
        rw [pow_one, ← hm, ← hf] at hz
        have h1 := add_mem hz (hIm _ hc)
        rwa [map_sub, AlgHom.commutes, sub_add_sub_cancel] at h1 }
  refine ⟨R, inferInstance, inferInstance, hco, f,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian I), AlgHom.ext fun z => ?_, fun R' _ _ _ g hg => ?_⟩
  · obtain ⟨c, hc⟩ := hx z
    have h1 := (res_eq_zero_iff Λ R _).2 (hIm _ hc)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hc
    rw [map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    exact h1.trans hc.symm
  · have hgI : I ≤ (maximalIdeal R').comap (g : A →+* R') := fun z hz =>
      (res_eq_zero_iff Λ R' _).1 ((AlgHom.congr_fun hg z).trans hz)
    obtain ⟨h, hh⟩ := lift_ex I (maximalIdeal R') (g : A →+* R') hgI
    have uniq : ∀ h₁ h₂ : R →ₐ[Λ] R', h₁.comp f = g → h₂.comp f = g → h₁ = h₂ := fun h₁ h₂ e₁ e₂ => by
      refine AlgHom.ext fun y => IsHausdorff.eq_iff_smodEq (I := maximalIdeal R') |>.2 fun n => ?_
      obtain ⟨z, hz⟩ := dense I fg n y
      have k : ∀ φ : R →ₐ[Λ] R', φ.comp f = g → φ y - g z ∈ maximalIdeal R' ^ n := fun φ e => by
        have hle : (I ^ n).map (algebraMap A R) ≤ (maximalIdeal R' ^ n).comap (φ : R →+* R') := by
          rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
          have e' : (φ : R →+* R').comp (algebraMap A R) = (g : A →+* R') := RingHom.ext fun w => AlgHom.congr_fun e w
          rw [e']
          exact (Ideal.pow_right_mono hgI n).trans (Ideal.le_comap_pow _ n)
        have h1 : φ (y - f z) ∈ maximalIdeal R' ^ n := hle hz
        rwa [map_sub, ← AlgHom.comp_apply φ f, e] at h1
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa using sub_mem (k h₁ e₁) (k h₂ e₂)
    let h' : R →ₐ[Λ] R' := { h with commutes' := fun c => (hh (algebraMap Λ A c)).trans (g.commutes c) }
    have e : h'.comp f = g := AlgHom.ext hh
    exact ⟨h', e, fun h₁ e₁ => uniq _ _ e₁ e⟩
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

theorem rank_le_of_lowest : ∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] (π : ℤ → V →ₗ[k] V) (T U : Submodule k V),
      (∀ p q x, π p (π q x) = if p = q then π q x else 0) → (∃ lo : ℤ, ∀ q < lo, π q = 0) →
      (∃ hi : ℤ, ∀ x, (∀ q < hi, π q x = 0) → x = 0) →
      (∀ p, ∀ x ∈ T, (∀ q < p, π q x = 0) → π p x ∈ U) → Module.rank k T ≤ Module.rank k U := by
  intro k V _ _ _ π T U h ⟨lo, hlo⟩ ⟨hi, hhi⟩ H
  let K : ℤ → Submodule k V := fun p => ⨅ q < p, LinearMap.ker (π q)
  have hK : ∀ p x, x ∈ K p ↔ ∀ q < p, π q x = 0 := fun p x => by simp [K, Submodule.mem_iInf]
  have step : ∀ (W : Submodule k V) p, Module.rank k ↥(W ⊓ K p) =
      Module.rank k ↥((W ⊓ K p).map (π p)) + Module.rank k ↥(W ⊓ K (p + 1)) := by
    intro W p
    rw [← LinearMap.rank_range_add_rank_ker ((π p).domRestrict (W ⊓ K p)), LinearMap.range_domRestrict]
    congr 1
    rw [LinearMap.ker_domRestrict]
    have e : W ⊓ K (p + 1) = (W ⊓ K p) ⊓ LinearMap.ker (π p) := by
      ext x
      simp only [Submodule.mem_inf, hK, LinearMap.mem_ker]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun q hq => h2 q (by omega)⟩, h2 p (by omega)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun q hq => ?_⟩
        rcases lt_or_eq_of_le (show q ≤ p by omega) with h4 | rfl
        exacts [h2 q h4, h3]
    rw [e, ← Submodule.map_comap_subtype (W ⊓ K p) (LinearMap.ker (π p))]
    exact (Submodule.equivMapOfInjective _ (W ⊓ K p).subtype_injective _).rank_eq
  have main : ∀ p ≤ max hi lo, Module.rank k ↥(T ⊓ K p) ≤ Module.rank k ↥(U ⊓ K p) := by
    intro p hp
    induction p using Int.inductionOn' (b := max hi lo) with
    | zero =>
      have : T ⊓ K (max hi lo) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hhi x fun q hq => (hK _ _).1 hx.2 q (lt_max_of_lt_left hq)
      rw [this]; simp
    | succ n hn ih => omega
    | pred n hn ih =>
      rw [step T, step U, sub_add_cancel]
      refine add_le_add (Submodule.rank_mono ?_) (ih hn)
      rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨π (n - 1) x, ⟨H _ x h1 ((hK _ _).1 h2), (hK _ _).2 fun q hq => ?_⟩, ?_⟩
      · rw [h, if_neg hq.ne]
      · rw [h, if_pos rfl]
  have top : K lo = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (hK _ _).2 fun q hq => by simp [hlo q hq]
  have := main lo (le_max_right _ _)
  rwa [top, inf_top_eq, inf_top_eq] at this

theorem tan_lowest : ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ), Symp m →
      (∀ g, Lim m (c.r g) (c₀.r g)) → (∀ v, Lim m (c.n v) (c₀.n v)) → ∀ p : ℤ, ∀ x ∈ Φ.Tan S c,
      (∀ g, FGe m p (x.1 g)) → (∀ v, FGe m p (x.2 v)) → Φ.cmpT m p x ∈ Φ.Tan S c₀ := by
  intro O Γ _ _ _ Φ k _ S c c₀ m hm hr hn p x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hX hY
  have c3 : ∀ {A B Z : M4 k}, FGe m 0 A → FGe m 0 B → FGe m p Z →
      FGe m p (A * Z * B) ∧ cmp m p (A * Z * B) = cmp m 0 A * cmp m p Z * cmp m 0 B := by
    intro A B Z hA hB hZ
    have h1 := (hA.mul hZ).mul hB
    have h2 := cmp_mul (hA.mul hZ) hB
    rw [cmp_mul hA hZ] at h2
    simp only [zero_add, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have csp : ∀ {Z : M4 k}, Z ∈ sp4 k → cmp m p Z ∈ sp4 k := by
    intro Z hZ
    show adj _ = -_
    rw [← cmp_adj hm, show adj Z = -Z from hZ, map_neg]
  have cz : ∀ {Z : M4 k} {i j}, Z i j = 0 → cmp m p Z i j = 0 := by
    intro Z i j h
    simp [cmp_apply, h]
  have cn : ∀ v {Z : M4 k}, FGe m p Z → adj (c₀.n v) * cmp m p Z * c₀.n v = cmp m p (adj (c.n v) * Z * c.n v) := by
    intro v Z hZ
    rw [(c3 ((hn v).1.adj hm) (hn v).1 hZ).2, cmp_adj hm, ← (hn v).2]
  refine ⟨a1.comp (cmp m p), fun g => csp (a2 g), fun g h => ?_, fun g h => ?_, fun i j h => cz (a5 h),
    fun g i j h1 h2 => ?_, fun v => ⟨csp (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
  · simp only [Fr.cmpT_fst]
    rw [a3, map_add (f := _), (c3 (hr g).1 (hr g⁻¹).1 (hX h)).2, ← (hr g).2, ← (hr g⁻¹).2]
  · rw [Fr.cmpT_fst, a4 g h, map_zero]
  · have := cmp_mul (hX g) (hr g).1
    rw [add_zero, ← (hr g).2] at this
    rw [Fr.cmpT_fst, ← this]
    exact cz (a6 g i j h1 h2)
  · rw [Fr.cmpT_snd, cn v (hY v)]
    exact cz ((a7 v).2 i j h)
  · have h3 := c3 (hr s).1 (hr s⁻¹).1 (hY v)
    rw [← (hr s).2, ← (hr s⁻¹).2] at h3
    rw [Fr.cmpT_snd, Fr.cmpT_fst, ← h3.2, ← map_add (f := _), ← map_sub, cn v (((hX s).add h3.1).sub (hY v))]
    exact cz (a8 v s hs i j h)

theorem tan_flow {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ) (hm : Symp m)
    (hr : ∀ g, Lim m (c.r g) (c₀.r g)) (hn : ∀ v, Lim m (c.n v) (c₀.n v)) :
    Module.rank k (Φ.TanS S c) ≤ Module.rank k (Φ.TanS S c₀) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i j, |m i - m j| < N :=
    ⟨∑ z : Fin 4 × Fin 4, |m z.1 - m z.2| + 1, fun i j => Int.lt_add_one_of_le
      (Finset.single_le_sum (f := fun z : Fin 4 × Fin 4 => |m z.1 - m z.2|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, j)))⟩
  have ge : ∀ {p : ℤ} {Z : M4 k}, (∀ q < p, cmp m q Z = 0) → FGe m p Z := by
    intro p Z h i j hij
    have := congrFun (congrFun (h _ hij) i) j
    simpa [cmp_apply] using this
  have cc : ∀ (p q : ℤ) (Z : M4 k), cmp m p (cmp m q Z) = if p = q then cmp m q Z else 0 := by
    intro p q Z
    ext i j
    by_cases h : p = q
    · subst h; simp only [cmp_apply, if_true]; split_ifs <;> rfl
    · simp only [cmp_apply, if_neg h, Matrix.zero_apply]
      split_ifs with h1 h2
      · omega
      all_goals rfl
  refine rank_le_of_lowest (Φ.cmpT m) _ _ (fun p q x => ?_) ⟨-N, fun q hq => ?_⟩ ⟨N, fun x hx => ?_⟩ fun p x hx h => ?_
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · rw [Fr.cmpT_fst, Fr.cmpT_fst, cc]; split_ifs <;> rfl
    · rw [Fr.cmpT_snd, Fr.cmpT_snd, cc]; split_ifs <;> rfl
  · have : ∀ Z : M4 k, cmp m q Z = 0 := fun Z => by
      ext i j
      have := abs_lt.1 (hN i j)
      rw [cmp_apply, if_neg (by omega)]; rfl
    exact LinearMap.ext fun x => Prod.ext (funext fun g => this _) (funext fun v => this _)
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_) <;> ext i j
    · exact ge (fun q hq => congrArg (·.1 g) (hx q hq)) i j (abs_lt.1 (hN i j)).2
    · exact ge (fun q hq => congrArg (·.2 v) (hx q hq)) i j (abs_lt.1 (hN i j)).2
  · exact tan_lowest Φ S c c₀ m hm hr hn p x hx (fun g => ge fun q hq => congrArg (·.1 g) (h q hq))
      fun v => ge fun q hq => congrArg (·.2 v) (h q hq)

end UpperTheory.V.Ws
end

section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Asm

section
variable {O Γ R R' : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing R'] {Φ : Fr O Γ} {a : O →+* R} {P : PD Φ.ι Γ R}

theorem res_map' (h : Φ.Res a P) (f : R →+* R') : Φ.Res (f.comp a) (P.map f) := by
  have e : ∀ (S : Finset (ℤ × ℤ)) (X : M4 R), SuppM S X → SuppM S (X.map f) := fun S X hX i j h1 h2 => by
    rw [Matrix.map_apply, hX i j h1 h2, map_zero]
  refine ⟨fun g i => congrArg f (h.diag g i), fun v s hs i => ?_, ?_⟩
  · rw [PD.map_ψ, h.char v s hs i]; rfl
  · exact h.shape.imp (fun k => ⟨fun g => e _ _ (k.1 g), fun v => e _ _ (k.2 v)⟩) fun k g => e _ _ (k g)

theorem isRes_map [TopologicalSpace Γ] (h : Φ.IsRes a P) (f : R →+* R') : Φ.IsRes (f.comp a) (P.map f) :=
  ⟨h.pair.map f, res_map' h.res f, h.cont.map f bot_le⟩

theorem pair_of (f : R →+* R') (hf : Function.Injective f) (h : Φ.IsPair (f.comp a) (P.map f)) : Φ.IsPair a P := by
  have hi : ∀ X Y : M4 R, X.map f = Y.map f → X = Y := fun X Y e => Matrix.map_injective hf e
  have z : ∀ x, f x = 0 → x = 0 := fun x => (map_eq_zero_iff f hf).1
  have gs : ∀ (ν : R) (X : M4 R), IsGSp (f ν) (X.map f) → IsGSp ν X := fun ν X k => by
    unfold IsGSp at k ⊢
    apply hi
    rw [Matrix.map_mul, ← adj_map, k]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine ⟨fun g => gs _ _ (h.mult g), fun g hg => hi _ _ ?_, fun i j hij => z _ (h.nrm hij),
    fun v => ⟨gs _ _ (by rw [map_one]; exact (h.low v).1), fun i => hf ?_, fun i j hij => z _ ((h.low v).2.2 i j hij)⟩,
    fun v s hs i j hij => z _ ?_, fun v s hs i => hf ?_⟩
  · exact (h.kill g hg).trans (Matrix.map_one f (map_zero f) (map_one f)).symm
  · rw [map_one]; exact (h.low v).2.1 i
  · have k := h.flag v s hs i j hij
    rwa [PD.map_flag] at k
  · rw [map_one, ← PD.map_ψ]; exact h.mu v s hs i

theorem linked_self [TopologicalSpace Γ] (h : Φ.IsRes a P) : Φ.Linked a P P := by
  have e : ∀ t : R, (P.map C).map (evalRingHom t) = P := fun t => by
    have : (evalRingHom t).comp C = RingHom.id R := by ext; simp
    rw [PD.map_map, this]; rfl
  exact ⟨P.map C, isRes_map h C, e 0, e 1⟩

theorem linked_isRes [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (h : Φ.Linked a P P') : Φ.IsRes a P' := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  have k := isRes_map hQ (evalRingHom 1)
  have : (evalRingHom (1 : R)).comp (C.comp a) = a := by ext; simp
  rwa [this] at k

theorem chain_end [TopologicalSpace Γ] {P' : PD Φ.ι Γ R} (hP : Φ.IsRes a P) (h : Φ.Chain a P P') :
    Φ.IsRes a P' ∧ Φ.Good a P' := by
  obtain ⟨hg, hc⟩ := h
  induction hc with
  | refl => exact ⟨hP, hg⟩
  | tail _ hl _ => exact ⟨linked_isRes hl.2, hl.1⟩

end

section
variable {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  {a : O →+* Λ} (X : Space Φ a) (J : Ideal X.B)

theorem end_pt {s t : PD Φ.ι Γ (ResidueField Λ)} (h : Φ.Linked ((residue Λ).comp a) s t) :
    ∃ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = t := by
  obtain ⟨Q, hQ, -, rfl⟩ := h
  obtain ⟨f, rfl, -⟩ := X.line Q hQ
  refine ⟨((aeval (1 : ResidueField Λ) : (ResidueField Λ)[X] →ₐ[ResidueField Λ] ResidueField Λ).restrictScalars Λ).comp f, ?_⟩
  rw [PD.map_map]
  congr 1

theorem someIn_of_locZero {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) (h : X.LocZero J y) {p : Ideal X.A}
    (hp : RingHom.ker y ≤ p) : X.SomeIn J p := by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  haveI : q.IsPrime := hq.1.1
  exact ⟨q, hq, hle.trans hp, Ideal.map_le_iff_le_comap.2 (h _ (Ideal.comap_isPrime _ q) fun s hs => hle hs)⟩

theorem zero_of_allIn {K : Type} [CommRing K] [IsDomain K] (y : X.A →+* K) {p : Ideal X.A} (h : X.AllIn J p)
    (hp : RingHom.ker y ≤ p) : ∀ b ∈ J, y (algebraMap X.B X.A b) = 0 := fun b hb => by
  haveI := RingHom.ker_isPrime y
  obtain ⟨q, hq, hle⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal X.A)) (J := RingHom.ker y) bot_le
  exact hle (h q hq (hle.trans hp) (Ideal.mem_map_of_mem _ hb))

end

theorem allIn_of_chain {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hΦ : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B)
    (hch : ∀ x : X.A →ₐ[Λ] ResidueField Λ, Φ.IsRes ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) →
      Φ.Good ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ)) → X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x))
    (x₀ x₁ : X.A →ₐ[Λ] ResidueField Λ) (hs : Φ.IsRes ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)))
    (hc : Φ.Chain ((residue Λ).comp a) (X.P.map (x₀ : X.A →+* ResidueField Λ)) (X.P.map (x₁ : X.A →+* ResidueField Λ)))
    (h₁ : X.SomeIn J (RingHom.ker x₁)) : X.AllIn J (RingHom.ker x₀) := by
  have key : ∀ s, Relation.ReflTransGen (fun x y => Φ.Good ((residue Λ).comp a) y ∧ Φ.Linked ((residue Λ).comp a) x y) s
      (X.P.map (x₁ : X.A →+* ResidueField Λ)) → Φ.IsRes ((residue Λ).comp a) s → Φ.Good ((residue Λ).comp a) s →
      ∀ x : X.A →ₐ[Λ] ResidueField Λ, X.P.map (x : X.A →+* ResidueField Λ) = s → X.AllIn J (RingHom.ker x) := by
    intro s h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro k1 k2 x e
      have hl : Φ.Linked ((residue Λ).comp a) (X.P.map (x : X.A →+* ResidueField Λ))
          (X.P.map (x₁ : X.A →+* ResidueField Λ)) := by
        rw [e]
        exact linked_self k1
      exact hch x (e ▸ k1) (e ▸ k2) ((conn Φ l a hΦ X J x x₁ hl).2 (hch x₁ k1 k2 h₁))
    | head hl _ ih =>
      rintro k1 k2 x rfl
      obtain ⟨x', rfl⟩ := end_pt X hl.2
      exact hch x k1 k2 ((conn Φ l a hΦ X J x x' hl.2).2 (ih (linked_isRes hl.2) hl.1 x' rfl))
  exact key _ hc.2 hs hc.1 x₀ rfl

end UpperTheory.V.Ws.Asm
end
