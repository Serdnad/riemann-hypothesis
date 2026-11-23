module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.Bundle002
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
public import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isLocallyConstant_finset_sum {S Y ι : Type} [TopologicalSpace S] [AddCommMonoid Y] (t : Finset ι)
    (f : ι → S → Y) (h : ∀ i ∈ t, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : Y)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsLocallyConstant.comp₂ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (· + ·)

private theorem cont_conj {S R : Type} [TopologicalSpace S] [CommRing R] (I : Ideal R) (x : S → M4 R) (a b : M4 R)
    (h : ∀ i j, AdicCont I fun s => x s i j) (i j : Fin 4) : AdicCont I fun s => (a * x s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j)) = fun s =>
      ∑ l, (∑ k, Ideal.Quotient.mk (I ^ N) (a i k) * Ideal.Quotient.mk (I ^ N) (x s k l)) *
        Ideal.Quotient.mk (I ^ N) (b l j) := by
    funext s

    simp [Matrix.mul_apply, map_sum, map_mul]
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j))
  rw [e]
  refine isLocallyConstant_finset_sum _ _ fun l _ => ?_
  refine IsLocallyConstant.comp₂ ?_ (IsLocallyConstant.const _) (· * ·)
  refine isLocallyConstant_finset_sum _ _ fun k _ => ?_
  exact IsLocallyConstant.comp₂ (IsLocallyConstant.const _) (h k l N) (· * ·)

private theorem cont_push {Λ S A A' : Type} [CommRing Λ] [IsLocalRing Λ] [TopologicalSpace S] [CommRing A] [Algebra Λ A]
    [IsCO Λ A] [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p : A →ₐ[Λ] A') (x : S → A)
    (h : AdicCont (maximalIdeal A) x) : AdicCont (maximalIdeal A') fun s => p (x s) := by
  intro N
  have hm : Ideal.map p (maximalIdeal A) ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff Λ A', res_map, res_eq_zero_iff]
    exact hy
  have hle : maximalIdeal A ^ N ≤ Ideal.comap p (maximalIdeal A' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hm N
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s))) =
      fun s => Ideal.quotientMap (maximalIdeal A' ^ N) (p : A →+* A') hle (Ideal.Quotient.mk (maximalIdeal A ^ N) (x s)) := by
    funext s
    rfl
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s)))
  rw [e]
  exact (h N).comp _

private theorem gsp_conj {R : Type} [CommRing R] {c : R} {x n : M4 R} (hx : IsGSp c x) (hn : IsGSp 1 n) :
    IsGSp c (adj n * x * n) := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have hn1 : adj n * n = 1 := by
    have := hn
    unfold IsGSp at this
    rw [this, one_smul]
  have hn2 : n * adj n = 1 := mul_eq_one_comm.mp hn1
  have hx' : adj x * x = c • 1 := hx
  show adj (adj n * x * n) * (adj n * x * n) = c • 1
  rw [hmul, hmul, hadj]
  calc adj n * (adj x * n) * (adj n * x * n) = adj n * (adj x * (n * adj n) * x) * n := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hn2, Matrix.mul_one, hx', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hn1]

private theorem gsp_push {Λ A A' : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing A'] [Algebra Λ A']
    (p : A →ₐ[Λ] A') {c : Λ} {x : M4 A} (hx : IsGSp (algebraMap Λ A c) x) : IsGSp (algebraMap Λ A' c) (x.map p) := by
  have := isGSp_map (p : A →+* A') hx
  rwa [AlgHom.coe_toRingHom, AlgHom.commutes] at this

theorem UpperTheory.V.Ws.X1.slEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∃ D : SL loc ν r n p, ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p' : A →ₐ[Λ] A') (p'' : A' →ₐ[Λ] R), p''.comp p' = p → ∃ D' : SL loc ν r n p'', (∀ s t, D'.om s t = (D.om s t).map p') ∧ ∀ v s, D'.de v s = (D.de v s).map p' := by
  intro Λ _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hker ν r n hν hW hr
  obtain ⟨yr, hyc, hym, hyp, -⟩ := X1.gspLift h2 p hp hker Γ (fun g => ν g) (fun g => r g) hν hr hW.mult
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨yn, -, hnm, hnp, -⟩ := X1.gspLift h2 p hp hker V (fun _ => 1) n
    (by intro N; exact IsLocallyConstant.of_discrete _)
    (by intro i j N; exact IsLocallyConstant.of_discrete _)
    (fun v => by simpa using hW.sp v)
  have hnm' : ∀ v, IsGSp 1 (yn v) := fun v => by simpa using hnm v
  have ht : ∀ v, ∃ y : Gv v → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧
      (∀ s, IsGSp (algebraMap Λ A (ν (loc v s))) (y s)) ∧
      (∀ s, (y s).map p = adj (n v) * r (loc v s) * n v) ∧ ∀ s, IsUp (y s) := by
    intro v
    obtain ⟨y, h1, h2', h3, h4⟩ := X1.gspLift h2 p hp hker (Gv v) (fun s => ν (loc v s))
      (fun s => adj (n v) * r (loc v s) * n v)
      (by intro N; exact (hν N).comp_continuous (hloc v))
      (by
        intro i j
        exact cont_conj _ _ _ _ (fun i j N => (hr i j N).comp_continuous (hloc v)) i j)
      (fun s => gsp_conj (hW.mult _) (hW.sp v))
    exact ⟨y, h1, h2', h3, h4 (hW.flag v)⟩
  choose yt hyt using ht
  let D : SL loc ν r n p := ⟨yr, hyc, hym, hyp, yn, hnm', hnp, yt, fun v => (hyt v).1, fun v => (hyt v).2.1,
    fun v => (hyt v).2.2.2, fun v => (hyt v).2.2.1⟩
  refine ⟨D, ?_⟩
  intro A' _ _ _ p' p'' hpp
  have hc : ∀ a, p'' (p' a) = p a := fun a => by rw [← hpp]; rfl
  have hmap : ∀ X : M4 A, (X.map p').map p'' = X.map p := fun X => by
    ext i j
    simp [hc]
  have hm1 : ∀ X Y : M4 A, (X * Y).map p' = X.map p' * Y.map p' := fun X Y => by
    ext i j

    simp [Matrix.mul_apply, map_sum]
  have hm2 : ∀ X Y : M4 A, (X - Y).map p' = X.map p' - Y.map p' := fun X Y => by
    ext i j
    simp
  have hadj : ∀ X : M4 A, adj (X.map p') = (adj X).map p' := fun X => adj_map (p' : A →+* A') X
  refine ⟨⟨fun g => (yr g).map p', ?_, ?_, ?_, fun v => (yn v).map p', ?_, ?_, fun v s => (yt v s).map p',
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    exact cont_push p' _ (hyc i j)
  · intro g
    exact gsp_push p' (hym g)
  · intro g
    rw [hmap, hyp]
  · intro v
    have := isGSp_map (p' : A →+* A') (hnm' v)
    simpa using this
  · intro v
    rw [hmap, hnp]
  · intro v i j
    exact cont_push p' _ ((hyt v).1 i j)
  · intro v s
    exact gsp_push p' ((hyt v).2.1 s)
  · intro v s i j hij
    simp [(hyt v).2.2.2 s i j hij]
  · intro v s
    rw [hmap]
    exact (hyt v).2.2.1 s
  · intro s t
    show (yr s).map p' * (yr t).map p' - (yr (s * t)).map p' = (yr s * yr t - yr (s * t)).map p'
    rw [hm2, hm1]
  · intro v s
    show (yr (loc v s)).map p' - (yn v).map p' * (yt v s).map p' * adj ((yn v).map p') =
      (yr (loc v s) - yn v * yt v s * adj (yn v)).map p'
    rw [hm2, hm1, hm1, hadj]
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem exProj {k W : Type} [Field k] [AddCommGroup W] [Module k W] (b n : Submodule k W)
    (h : IsCompl b n) : ∃ P : W →ₗ[k] W, (∀ x, P x ∈ n) ∧ ∀ x, P x - x ∈ b := by
  refine ⟨n.projection b h.symm, fun x => Submodule.projection_apply_mem _ x, fun x => ?_⟩
  have e := Submodule.projection_add_projection_eq_self h.symm x
  have hm : b.projection n h x ∈ b := Submodule.projection_apply_mem _ x
  have : n.projection b h.symm x - x = -(b.projection n h x) := by
    calc n.projection b h.symm x - x
        = n.projection b h.symm x - (n.projection b h.symm x + b.projection n h x) := by rw [e]
      _ = -(b.projection n h x) := by abel
  rw [this]
  exact b.neg_mem hm

private theorem dimLem {k W T H A : Type} [Field k] [AddCommGroup W] [Module k W] [Module.Finite k W]
    [AddCommGroup T] [Module k T] [AddCommGroup H] [Module k H] [AddCommGroup A] [Module k A] [Module.Finite k A]
    (t H0 : Submodule k W) (e : T →ₗ[k] W ⧸ t) (j : LinearMap.ker e →ₗ[k] A) (hj : Function.Injective j)
    (q : T →ₗ[k] H) (hq : Function.Surjective q) (f : W →ₗ[k] T) (hf : ∀ X, q (f X) = 0)
    (h0 : LinearMap.ker f ≤ H0) :
    Module.finrank k H + Module.finrank k t ≤ Module.finrank k A + Module.finrank k H0 := by
  haveI hK : Module.Finite k (LinearMap.ker e) := Module.Finite.of_injective j hj
  haveI hT : Module.Finite k T := by
    rw [← Module.rank_lt_aleph0_iff, ← LinearMap.rank_range_add_rank_ker e]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 k _) (Module.rank_lt_aleph0 k _)
  have r1 := LinearMap.finrank_range_add_finrank_ker e
  have r2 := Submodule.finrank_le (LinearMap.range e)
  have r3 := Submodule.finrank_quotient_add_finrank t
  have r4 := LinearMap.finrank_le_finrank_of_injective hj
  have r5 := LinearMap.finrank_range_add_finrank_ker q
  have r6 : Module.finrank k (LinearMap.range q) = Module.finrank k H := by
    rw [LinearMap.range_eq_top.mpr hq, finrank_top]
  have hfq : LinearMap.range f ≤ LinearMap.ker q := by
    rintro _ ⟨X, rfl⟩
    exact hf X
  have r7 := Submodule.finrank_mono hfq
  have r8 := LinearMap.finrank_range_add_finrank_ker f
  have r9 := Submodule.finrank_mono h0
  omega

theorem UpperTheory.V.Ws.X1.coneTan :
    ∀ {k G W V : Type} [Field k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W] [Module.Finite k W] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b n : V → Submodule k W) (g0 : G) (t : Submodule k W), (∀ X, IsLocallyConstant fun g => ρ g X) → (∀ v s, ∀ X ∈ b v, ρ (loc v s) X ∈ b v) → (∀ v, IsCompl (b v) (n v)) → Module.Finite k (TanC loc ρ b n g0 t) → Module.finrank k (Fr.H1C loc ρ b) + Module.finrank k t ≤ Module.finrank k (TanC loc ρ b n g0 t) + Module.finrank k (Fr.coneH0 ρ b) := by
  intro k G W V _ _ _ _ _ _ Gv _ loc ρ b n g0 t hlc hstab hcompl hfin
  choose P hPn hPb using fun v => exProj (b v) (n v) (hcompl v)
  have hPb' : ∀ v x, x - P v x ∈ b v := fun v x => by
    simpa using (b v).neg_mem (hPb v x)
  have hloc : ∀ v (s : Gv v) (y : W), y ∈ b v → ρ (loc v s) y - y ∈ b v := fun v s y hy =>
    (b v).sub_mem (hstab v s y hy) hy
  set S : Submodule k ((G → W) × (V → W)) :=
    Fr.Z1C loc ρ b ⊓ Submodule.comap (LinearMap.snd k (G → W) (V → W)) (Submodule.pi Set.univ n) with hSd
  let q : S →ₗ[k] Fr.H1C loc ρ b :=
    (Submodule.mkQ _) ∘ₗ Submodule.inclusion (inf_le_left : S ≤ Fr.Z1C loc ρ b)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨⟨c, x⟩, hz⟩ := z
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have hmem : ((c, fun v => P v (x v)) : (G → W) × (V → W)) ∈ S := by
      refine ⟨⟨hz1, hz2, fun v s => ?_⟩, ?_⟩
      · have h1 := hz3 v s
        have h2 := hloc v s _ (hPb v (x v))
        have e : c (loc v s) - (ρ (loc v s) (P v (x v)) - P v (x v)) =
            (c (loc v s) - (ρ (loc v s) (x v) - x v)) -
              (ρ (loc v s) (P v (x v) - x v) - (P v (x v) - x v)) := by
          rw [map_sub]; abel
        simp only at h1 ⊢
        rw [e]
        exact (b v).sub_mem h1 h2
      · simp [Submodule.mem_pi, hPn]
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    refine ⟨0, fun s => ?_, fun v => ?_⟩
    · simp
    · simpa using hPb v (x v)
  have fmem : ∀ X : W, ((fun s => ρ s X - X, fun v => P v X) : (G → W) × (V → W)) ∈ S := by
    intro X
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact (hlc X).sub (IsLocallyConstant.const X)
    · intro s u
      simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro v s
      have h2 := hloc v s _ (hPb' v X)
      have e : (ρ (loc v s) X - X) - (ρ (loc v s) (P v X) - P v X) =
          ρ (loc v s) (X - P v X) - (X - P v X) := by
        rw [map_sub]; abel
      simp only
      rw [e]
      exact h2
    · simp [Submodule.mem_pi, hPn]
  let f : W →ₗ[k] S :=
    { toFun := fun X => ⟨_, fmem X⟩
      map_add' := fun X Y => by
        apply Subtype.ext
        ext s <;> simp <;> abel
      map_smul' := fun a X => by
        apply Subtype.ext
        ext s <;> simp [smul_sub] }
  have hf : ∀ X, q (f X) = 0 := by
    intro X
    simp only [q, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨X, fun s => rfl, fun v => hPb v X⟩
  have h0 : LinearMap.ker f ≤ Fr.coneH0 ρ b := by
    intro X hX
    rw [LinearMap.mem_ker] at hX
    have h1 := congrArg (fun z : S => z.1.1) hX
    have h2 := congrArg (fun z : S => z.1.2) hX
    refine ⟨fun g => ?_, fun v => ?_⟩
    · have := congrFun h1 g
      simp [f] at this
      exact sub_eq_zero.mp this
    · have := congrFun h2 v
      have hb := hPb v X
      simp [f] at this
      rw [this, zero_sub] at hb
      simpa using (b v).neg_mem hb
  let e : S →ₗ[k] W ⧸ t :=
    t.mkQ ∘ₗ (LinearMap.proj g0 ∘ₗ LinearMap.fst k (G → W) (V → W)) ∘ₗ S.subtype
  have jmem : ∀ z : LinearMap.ker e, (z.1.1 : (G → W) × (V → W)) ∈ TanC loc ρ b n g0 t := by
    rintro ⟨⟨z, hz1, hz2⟩, hze⟩
    rw [LinearMap.mem_ker] at hze
    refine ⟨hz1, ?_, ?_⟩
    · simpa [e, Submodule.Quotient.mk_eq_zero] using hze
    · exact hz2
  let j : LinearMap.ker e →ₗ[k] TanC loc ρ b n g0 t :=
    LinearMap.codRestrict _ (S.subtype ∘ₗ (LinearMap.ker e).subtype) jmem
  have hj : Function.Injective j := by
    intro z z' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)
  haveI : Module.Finite k (TanC loc ρ b n g0 t) := hfin
  exact dimLem t (Fr.coneH0 ρ b) e j hj q hq f hf h0
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gen_of_max {A : Type} [CommGroup A] (l : ℕ)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n)
    (a : ℕ) (z : A) (h1 : z ^ l ^ (a + 1) = 1) (h0 : z ^ l ^ a ≠ 1) :
    ∀ b, b ≤ a + 1 → ∀ s : A, s ^ l ^ b = 1 → s ∈ Subgroup.zpowers z := by
  intro b
  induction b with
  | zero => intro _ s hs; simp at hs; simp [hs]
  | succ b ih =>
    intro hb s hs
    obtain ⟨n, hn⟩ := hl (z ^ l ^ a) (s ^ l ^ b) (by rw [← pow_mul, ← pow_succ, h1])
      (by rw [← pow_mul, ← pow_succ, hs]) h0
    obtain ⟨c, rfl⟩ : ∃ c, a = c + b := ⟨a - b, by omega⟩
    have h2 : (s / z ^ (l ^ c * n)) ^ l ^ b = 1 := by
      rw [div_pow, hn, ← pow_mul, ← pow_mul, pow_add, mul_right_comm, div_self']
    have h3 := ih (by omega) _ h2
    have h4 := mul_mem h3 (Subgroup.npow_mem_zpowers z (l ^ c * n))
    rwa [div_mul_cancel] at h4

private theorem cyc_abs {A : Type} [CommGroup A] (l : ℕ) (hp : l.Prime)
    (hres : ∀ x : A, x ≠ 1 → ∃ U : Subgroup A, U.index ≠ 0 ∧ x ∉ U)
    (hl : ∀ s t : A, s ^ l = 1 → t ^ l = 1 → s ≠ 1 → ∃ n : ℕ, t = s ^ n) :
    ∃ z : A, (∃ a, z ^ l ^ a = 1) ∧ ∀ s : A, (∃ a, s ^ l ^ a = 1) → ∃ n : ℕ, s = z ^ n := by
  classical
  by_cases hx : ∃ x : A, x ^ l = 1 ∧ x ≠ 1
  · obtain ⟨x, hx1, hx0⟩ := hx
    obtain ⟨U, hU, hxU⟩ := hres x hx0
    let P : ℕ → Prop := fun a => ∃ s : A, s ^ l ^ (a + 1) = 1 ∧ s ^ l ^ a ≠ 1
    have hP0 : P 0 := ⟨x, by simpa using hx1, by simpa using hx0⟩
    have hbd : ∀ a, P a → a ≤ U.index := by
      rintro a ⟨s, h1, h0⟩
      by_contra hlt
      obtain ⟨n, hn⟩ := hl (s ^ l ^ a) x (by rw [← pow_mul, ← pow_succ, h1]) hx1 h0
      apply hxU
      rw [hn]
      apply pow_mem
      have d1 : orderOf (QuotientGroup.mk' U s) ∣ l ^ (a + 1) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← map_pow, h1, map_one]
      have d2 : orderOf (QuotientGroup.mk' U s) ∣ U.index := orderOf_dvd_natCard _
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 d1
      have d3 : l ^ j ≤ U.index := hj ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero hU) d2
      have d4 : j < l ^ j := Nat.lt_pow_self hp.one_lt
      have d5 : orderOf (QuotientGroup.mk' U s) ∣ l ^ a := hj ▸ pow_dvd_pow l (by omega)
      have d6 := orderOf_dvd_iff_pow_eq_one.1 d5
      rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at d6
      exact d6
    obtain ⟨z, h1, h0⟩ : P (Nat.findGreatest P U.index) := Nat.findGreatest_spec (Nat.zero_le _) hP0
    refine ⟨z, ⟨_, h1⟩, ?_⟩
    rintro s ⟨c, hc⟩
    have key : ∀ c, s ^ l ^ c = 1 → s ^ l ^ (Nat.findGreatest P U.index + 1) = 1 := by
      intro c
      induction c with
      | zero => intro h; simp at h; simp [h]
      | succ c ih =>
        intro h
        by_cases h' : s ^ l ^ c = 1
        · exact ih h'
        · have hPc : P c := ⟨s, h, h'⟩
          have := Nat.le_findGreatest (hbd c hPc) hPc
          exact orderOf_dvd_iff_pow_eq_one.1
            ((orderOf_dvd_of_pow_eq_one h).trans (pow_dvd_pow l (by omega)))
    have hm := gen_of_max l hl _ z h1 h0 _ le_rfl s (key c hc)
    have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨_, pow_pos hp.pos _, h1⟩
    obtain ⟨n, hn⟩ := hf.mem_powers_iff_mem_zpowers.2 hm
    exact ⟨n, hn.symm⟩
  · refine ⟨1, ⟨0, by simp⟩, ?_⟩
    rintro s ⟨c, hc⟩
    refine ⟨0, ?_⟩
    rw [pow_zero]
    induction c with
    | zero => simpa using hc
    | succ c ih =>
      apply ih
      by_contra h
      exact hx ⟨_, by rw [← pow_mul, ← pow_succ, hc], h⟩

theorem UpperTheory.V.Ws.X1.muCyc :
    ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (l : ℕ) [Fact l.Prime] (H : Subgroup Γ), IsClosed (H : Set Γ) → (∀ s ∈ H, ∀ t ∈ H, s ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → t ^ l ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → s ∉ (⁅H, H⁆ : Subgroup Γ).topologicalClosure → ∃ n : ℕ, t * (s ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure) → ∃ ζ, MuGen H (muOf l H) ζ := by
  intro Γ _ _ _ _ _ _ l hp H hH hl
  unfold MuGen muOf
  have hcl : IsClosed (((⁅H, H⁆ : Subgroup Γ).topologicalClosure : Subgroup Γ) : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  have hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure :=
    fun a ha b hb => Subgroup.le_topologicalClosure _ (Subgroup.commutator_mem_commutator ha hb)
  generalize (⁅H, H⁆ : Subgroup Γ).topologicalClosure = C at hl hcl hcomm ⊢
  haveI hN : (C.subgroupOf H).Normal := ⟨fun c hc h => by
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using mul_mem (hcomm h h.2 c c.2) hc⟩
  let π := QuotientGroup.mk' (C.subgroupOf H)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have h1 : ∀ x : H, π x = 1 ↔ (x : Γ) ∈ C := fun x => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  have h2 : ∀ x y : H, π x = π y ↔ (x : Γ) * (y : Γ)⁻¹ ∈ C := fun x y => by
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul, h1]; simp
  letI : CommGroup (H ⧸ C.subgroupOf H) :=
    { (inferInstance : Group (H ⧸ C.subgroupOf H)) with
      mul_comm := fun a b => by
        obtain ⟨a, rfl⟩ := hπ a
        obtain ⟨b, rfl⟩ := hπ b
        rw [← map_mul, ← map_mul, h2]
        simpa [mul_assoc] using hcomm a a.2 b b.2 }
  refine (cyc_abs (A := H ⧸ C.subgroupOf H) l hp.out ?_ ?_).elim ?_
  rotate_left 2
  · rintro z ⟨⟨a, ha⟩, hz⟩
    obtain ⟨z, rfl⟩ := hπ z
    refine ⟨z, ⟨z.2, a, ?_⟩, ?_⟩
    · rw [← map_pow, h1] at ha
      simpa using ha
    · rintro s ⟨hs, c, hc⟩
      obtain ⟨n, hn⟩ := hz (π ⟨s, hs⟩) ⟨c, by rw [← map_pow, h1]; simpa using hc⟩
      rw [← map_pow, h2] at hn
      exact ⟨n, by simpa using hn⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := hπ x
    have ho : IsOpen {g : Γ | (x : Γ) * g ∉ C} :=
      hcl.isOpen_compl.preimage (continuous_const_mul (x : Γ))
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho
      (by simpa [← h1] using hx)
    refine ⟨(N.toSubgroup.subgroupOf H).map π, ?_, ?_⟩
    · refine ne_zero_of_dvd_ne_zero ?_ (Subgroup.index_map_dvd _ hπ)
      haveI : Finite (Γ ⧸ N.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ N.isOpen'
      haveI : N.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      exact Subgroup.FiniteIndex.index_ne_zero
    · rintro ⟨n, hn, e⟩
      have hn' : (n : Γ)⁻¹ ∈ N.toSubgroup := inv_mem (Subgroup.mem_subgroupOf.1 hn)
      exact hN hn' ((h2 x n).1 e.symm)
  · intro s t hs ht h0
    obtain ⟨s, rfl⟩ := hπ s
    obtain ⟨t, rfl⟩ := hπ t
    rw [← map_pow, h1] at hs ht
    obtain ⟨n, hn⟩ := hl s s.2 t t.2 (by simpa using hs) (by simpa using ht) (by rwa [← h1])
    exact ⟨n, by rw [← map_pow, h2]; simpa using hn⟩
end
