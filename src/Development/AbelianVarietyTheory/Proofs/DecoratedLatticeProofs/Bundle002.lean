module

public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

section

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.ChainOnto

theorem exists_orthonormal_expansion_of_sesq {C : Type} [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C]
    (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ip x y = conj (ip y x))
    (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re) :
    ∃ (n : ℕ) (b : Fin n → C), (∀ i j, ip (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x, x = ∑ i, ip x (b i) • b i := by
  let cd : InnerProductSpace.Core ℂ C :=
    { inner := fun x y => ip y x
      conj_inner_symm := fun x y => by simp [hsym y x]
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · exact (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        change ip x x = 0 at hx
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup C := @InnerProductSpace.Core.toNormedAddCommGroup ℂ C _ _ _ cd
  letI : InnerProductSpace ℂ C := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ C
  refine ⟨_, b, fun i j => ?_, fun x => ?_⟩
  · have h := orthonormal_iff_ite.mp b.orthonormal j i
    have e : ⟪b j, b i⟫_ℂ = ip (b i) (b j) := rfl
    rw [e] at h
    rw [h]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have h := b.sum_repr' x
    exact h.symm

theorem value_of_adjoint_of_mem_span : ∀ (X W C : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ev : C →ₗ[ℂ] W →ₗ[ℂ] (X → ℂ)) (K : Submodule ℂ W) (ipD : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (pet : (X → ℂ) → (X → ℂ) → ℂ), (∀ w w', ipD w w' = conj (ipD w' w)) → (∀ w, w ≠ 0 → 0 < (ipD w w).re) → (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → (∀ (y : C) (w : W) (n : ℕ) (ys : Fin n → C) (ws : Fin n → W), pet (ev y w) (∑ i, ev (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i)) → ∀ (x : C) (F : X → ℂ) (l : W → ℂ), F ∈ Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} → (∀ y, ∀ w ∈ K, pet (ev y w) F = ip y x * l w) → F ≠ 0 → x ≠ 0 ∧ ∃ w ∈ K, F = ev x w := by
  intro X W C _ _ _ _ _ ev K ipD ip pet hD hDpos hsym hpos hpet x F l hF hl hF0
  obtain ⟨n, b, hb, hexp⟩ := exists_orthonormal_expansion_of_sesq ip hsym hpos
  let Φ : (Fin n → W) →ₗ[ℂ] (X → ℂ) := ∑ j, (ev (b j)).comp (LinearMap.proj j)
  have hΦ : ∀ u, Φ u = ∑ j, ev (b j) (u j) := by
    intro u; simp [Φ, LinearMap.sum_apply]
  have hspan : Submodule.span ℂ {G | ∃ y, ∃ w ∈ K, G = ev y w} ≤
      (Submodule.pi Set.univ (fun _ : Fin n => K)).map Φ := by
    rw [Submodule.span_le]
    rintro G ⟨y, w, hw, rfl⟩
    refine ⟨fun j => ip y (b j) • w, fun j _ => K.smul_mem _ hw, ?_⟩
    rw [hΦ]
    conv_rhs => rw [hexp y]

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_smul, LinearMap.smul_apply]
  obtain ⟨u, hu, hFu⟩ := hspan hF
  have huK : ∀ j, u j ∈ K := fun j => hu j (Set.mem_univ j)
  rw [hΦ] at hFu
  have key : ∀ k, ∀ w ∈ K, ipD w (u k) = ip (b k) x * l w := by
    intro k w hw
    have h1 := hl (b k) w hw
    rw [← hFu, hpet] at h1
    simpa only [hb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using h1
  have hex : ∃ k, u k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hF0
    rw [← hFu]
    simp [h]
  obtain ⟨k, hk⟩ := hex
  have hkpos := hDpos (u k) hk
  rw [key k (u k) (huK k)] at hkpos
  have ha : ip (b k) x ≠ 0 := by
    intro h; rw [h, zero_mul] at hkpos; simp at hkpos
  have hx : x ≠ 0 := by
    rintro rfl; exact ha (by simp)
  refine ⟨hx, ?_⟩
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀, w₀ = (conj (ip (b k) x))⁻¹ • u k := ⟨_, rfl⟩
  have hw₀K : w₀ ∈ K := hw₀def ▸ K.smul_mem _ (huK k)
  have hw₀ : ∀ w ∈ K, ipD w w₀ = l w := by
    intro w hw
    rw [hw₀def, LinearMap.map_smulₛₗ, key k w hw, map_inv₀, Complex.conj_conj, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hu_eq : ∀ j, u j = conj (ip (b j) x) • w₀ := by
    intro j
    have hdK : u j - conj (ip (b j) x) • w₀ ∈ K := K.sub_mem (huK j) (K.smul_mem _ hw₀K)
    have hd0 : ∀ w ∈ K, ipD w (u j - conj (ip (b j) x) • w₀) = 0 := by
      intro w hw
      rw [map_sub, LinearMap.map_smulₛₗ, key j w hw, hw₀ w hw, Complex.conj_conj, smul_eq_mul, sub_self]
    by_contra hne
    have := hDpos _ (sub_ne_zero.mpr hne)
    rw [hd0 _ hdK] at this
    simp at this
  refine ⟨w₀, hw₀K, ?_⟩
  rw [← hFu]
  have hsum : ∑ j, ev (b j) (u j) = ∑ j, ev (b j) (conj (ip (b j) x) • w₀) :=
    Finset.sum_congr rfl (fun j _ => by rw [hu_eq j])
  rw [hsum]
  conv_rhs => rw [hexp x]

  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [map_smul, LinearMap.smul_apply]
  rw [hsym x (b j)]

end GlobalTheory.ChainOnto
end

section

open scoped ComplexConjugate

namespace GlobalTheory.ChainOnto

theorem exists_sum_pairwise_unrelated {A I : Type} [AddCommGroup A] [Module ℂ A]
    (pA : A → I → Prop) (RA : I → I → Prop) (hRA : Equivalence RA)
    (hmerge : ∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hsmul : ∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) (u : A)
    (hu : u ∈ Submodule.span ℂ {u | ∃ B, pA u B}) :
    ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i := by
  classical
  let Q : A → Prop := fun u => ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i
  have hQ0 : Q 0 := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  have hadd1 : ∀ u w B, Q u → pA w B → Q (u + w) := by
    rintro u w B ⟨s, v, hv, hp, rfl⟩ hw
    by_cases hex : ∃ i ∈ s, RA i B
    · obtain ⟨i, hi, hiB⟩ := hex
      by_cases hz : v i + w = 0
      · refine ⟨s.erase i, v, fun j hj => hv j (Finset.mem_of_mem_erase hj),
          fun j hj j' hj' => hp j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj'), ?_⟩
        rw [← Finset.add_sum_erase s v hi]
        calc v i + ∑ x ∈ s.erase i, v x + w = (v i + w) + ∑ x ∈ s.erase i, v x := by abel
          _ = _ := by rw [hz, zero_add]
      · refine ⟨s, Function.update v i (v i + w), ?_, hp, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have := hmerge (v j) w j B 1 (hv j hj) hw hiB (by simpa using hz)
            simpa using this
          · rw [Function.update_of_ne hji]; exact hv j hj
        · rw [← Finset.add_sum_erase s (Function.update v i (v i + w)) hi, ← Finset.add_sum_erase s v hi]
          simp only [Function.update_self]
          rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)]
          abel
    · push_neg at hex
      have hBs : B ∉ s := fun hB => hex B hB (hRA.refl B)
      refine ⟨insert B s, Function.update v B w, ?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with hj | hj
        · subst hj; simpa using hw
        · have hjB : j ≠ B := fun h => hBs (by rw [← h]; exact hj)
          rw [Function.update_of_ne hjB]; exact hv j hj
      · intro j hj j' hj' hne
        rw [Finset.mem_insert] at hj hj'
        rcases hj with hj | hj <;> rcases hj' with hj' | hj'
        · exact absurd (hj.trans hj'.symm) hne
        · subst hj; exact fun h => hex j' hj' (hRA.symm h)
        · subst hj'; exact hex j hj
        · exact hp j hj j' hj' hne
      · rw [Finset.sum_insert hBs, Function.update_self,
          Finset.sum_congr rfl (fun j hj => Function.update_of_ne (show j ≠ B from fun h => hBs (by rw [← h]; exact hj)) w v)]
        abel
  have haddS : ∀ (s' : Finset I) (v' : I → A) u, Q u → (∀ i ∈ s', pA (v' i) i) →
      Q (u + ∑ i ∈ s', v' i) := by
    intro s' v'
    induction s' using Finset.induction_on with
    | empty => intro u hu _; simpa using hu
    | insert a s ha ih =>
      intro u hu hv'
      rw [Finset.sum_insert ha, ← add_assoc]
      exact ih _ (hadd1 u (v' a) a hu (hv' a (Finset.mem_insert_self a s)))
        (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
  have hadd : ∀ u u', Q u → Q u' → Q (u + u') := by
    rintro u u' hu ⟨s', v', hv', -, rfl⟩
    exact haddS s' v' u hu hv'
  have hsm : ∀ (a : ℂ) u, Q u → Q (a • u) := by
    rintro a u ⟨s, v, hv, hp, rfl⟩
    by_cases ha : a = 0
    · subst ha; simpa using hQ0
    · exact ⟨s, fun i => a • v i, fun i hi => hsmul _ _ a (hv i hi) ha, hp, by rw [Finset.smul_sum]⟩
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B, hB⟩ := hx
    simpa using hadd1 0 x B hQ0 hB
  | zero => exact hQ0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsm a x hx

theorem exists_ne_zero_orth {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (hsym : ∀ x y, ipA x y = conj (ipA y x))
    (S : Submodule ℂ A) (hS : S ≠ ⊤) : ∃ u : A, u ≠ 0 ∧ ∀ s ∈ S, ipA s u = 0 := by
  classical
  let b := Module.finBasis ℂ S
  let f : A →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    { toFun := fun u i => ipA u (b i : A)
      map_add' := by intro x y; ext i; simp
      map_smul' := by intro a x; ext i; simp }
  have hlt : Module.finrank ℂ (Fin (Module.finrank ℂ S) → ℂ) < Module.finrank ℂ A := by
    rw [Module.finrank_fin_fun]
    exact Submodule.finrank_lt hS
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨u, hu0, fun s hs => ?_⟩
  have hzero : (ipA u).comp S.subtype = 0 := by
    refine b.ext fun i => ?_
    have := congrFun (LinearMap.mem_ker.mp hu) i
    simpa [f] using this
  have : ipA u s = 0 := by
    have := LinearMap.congr_fun hzero ⟨s, hs⟩
    simpa using this
  rw [hsym, this, map_zero]

theorem surjective_of_adjoint_separates : ∀ (A C I J : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ A] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ) (Θ : C →ₗ[ℂ] A) (pA : A → I → Prop) (pC : C → J → Prop) (RA : I → I → Prop) (RC : J → J → Prop) (T : I → J), (∀ x y, ipA x y = conj (ipA y x)) → (∀ x, x ≠ 0 → 0 < (ipA x x).re) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → Equivalence RA → Submodule.span ℂ {u | ∃ B, pA u B} = ⊤ → (∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B) → (∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) → (∀ B B', RC (T B) (T B') → RA B B') → (∀ (ι : Type) (x : ι → C) (B : ι → J), (∀ i, pC (x i) (B i)) → (∀ i i', i ≠ i' → ¬ RC (B i) (B i')) → LinearIndependent ℂ x) → (∀ u B, pA u B → ∃ x, (∀ y, ip y x = ipA (Θ y) u) ∧ pC x (T B)) → Function.Surjective Θ := by
  intro A C I J _ _ _ _ _ ipA ip Θ pA pC RA RC T hsym _ hpos hRA hspan hmerge hsmul hRCA hli hex
  classical
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨u, hu0, horth⟩ := exists_ne_zero_orth ipA hsym _ hne
  have horth' : ∀ y, ipA (Θ y) u = 0 := fun y => horth _ (LinearMap.mem_range_self Θ y)
  obtain ⟨s, v, hv, hp, hus⟩ := exists_sum_pairwise_unrelated pA RA hRA hmerge hsmul u
    (by rw [hspan]; exact Submodule.mem_top)
  have hs : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hu0 (by simpa using hus)
  have hx : ∀ i : s, ∃ x, (∀ y, ip y x = ipA (Θ y) (v i)) ∧ pC x (T i) :=
    fun i => hex _ _ (hv i i.2)
  choose x hx1 hx2 using hx
  have hlin := hli s x (fun i => T i) hx2
    (fun i i' hne hR => hp i i.2 i' i'.2 (fun h => hne (Subtype.ext h)) (hRCA _ _ hR))
  have hzy : ∀ y, ip y (∑ i, x i) = 0 := by
    intro y

    rw [map_sum]
    simp_rw [hx1]

    rw [← map_sum, Finset.sum_coe_sort s v, ← hus, horth']
  have hz : ∑ i, x i = 0 := by
    by_contra h
    have := hpos _ h
    rw [hzy] at this
    simp at this
  obtain ⟨i, hi⟩ := hs
  have := Fintype.linearIndependent_iff.mp hlin (fun _ => 1) (by simpa using hz) ⟨i, hi⟩
  exact one_ne_zero this

end GlobalTheory.ChainOnto
end

section

open scoped ContDiff

namespace GlobalTheory.PolyOfDeriv

theorem taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2

theorem foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this

theorem multilinear_diag_poly {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]

  rw [hx, M.map_sum]

  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]

theorem eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]

  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp

end GlobalTheory.PolyOfDeriv
end

section

open Matrix

namespace GlobalTheory

theorem matrix_pow_mul_eq_mul_pow_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem matrix_hasSum_exp {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) (NormedSpace.exp X) := by
  let _ : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X

theorem matrix_exp_mul_eq_mul_exp_of_intertwine {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) :
    NormedSpace.exp X * ε = ε * NormedSpace.exp β := by
  let g : Matrix (Fin m) (Fin m) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => A * ε) (fun A B => Matrix.add_mul A B ε)
  have hg : Continuous g := Continuous.matrix_mul continuous_id continuous_const
  let g' : Matrix (Fin r) (Fin r) ℂ →+ Matrix (Fin m) (Fin r) ℂ :=
    AddMonoidHom.mk' (fun A => ε * A) (fun A B => Matrix.mul_add ε A B)
  have hg' : Continuous g' := Continuous.matrix_mul continuous_const continuous_id
  have hL := (matrix_hasSum_exp X).map g hg
  have hR := (matrix_hasSum_exp β).map g' hg'
  have key : (g ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • X ^ n) =
      (g' ∘ fun n : ℕ => ((n.factorial : ℂ)⁻¹) • β ^ n) := by
    funext n
    simp only [Function.comp, g, g', AddMonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul,
      matrix_pow_mul_eq_mul_pow_of_intertwine X ε β h n]
  rw [key] at hL
  exact hL.unique hR

theorem matrix_exp_smul_mul_eq_mul_exp_smul_of_intertwine :
    ∀ (m r : ℕ) (X : Matrix (Fin m) (Fin m) ℂ) (ε : Matrix (Fin m) (Fin r) ℂ)
      (β : Matrix (Fin r) (Fin r) ℂ), X * ε = ε * β →
      ∀ s : ℝ, NormedSpace.exp (s • X) * ε = ε * NormedSpace.exp (s • β) := by
  intro m r X ε β h s
  apply matrix_exp_mul_eq_mul_exp_of_intertwine
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

end GlobalTheory
end
