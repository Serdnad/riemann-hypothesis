module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ramCard :
    ∀ (R D M : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M), (∀ g, ρ g = 1) → m0 ≠ 0 → Finite (H1 ρ) →
      ∀ φ₁ ∈ Z1 (Representation.trivial R D R), ∀ φ₂ ∈ Z1 (Representation.trivial R D R), (∀ g ∈ I, φ₁ g = 0) → (∃ g, φ₁ g = 1) → (∃ g ∈ I, φ₂ g = 1) →
      2 * Nat.card M ≤ Nat.card (ramLine ρ I m0) := by
  rintro R D M _ _ _ _ _ _ _ _ _ _ ρ I m0 hρ hm0 _ φ₁ hφ₁ φ₂ hφ₂ hI1 ⟨g1, hg1⟩ ⟨g2, hg2I, hg2⟩
  obtain ⟨c1, a1⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₁
  obtain ⟨c2, a2⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₂
  let fn : R → M → D → M := fun t m g => φ₁ g • m + (t * φ₂ g) • m0
  have hz : ∀ t m, fn t m ∈ Z1 ρ := by
    intro t m
    rw [mem_Z1_iff_cocycle]
    refine ⟨(continuous_of_discreteTopology (f := fun p : R × R => p.1 • m + (t * p.2) • m0)).comp
      (c1.prodMk c2), ?_⟩
    intro g h
    simp [fn, hρ g, a1 g h, a2 g h, add_smul, mul_add] <;> abel
  let F : Bool × M → ramLine ρ I m0 := fun p =>
    ⟨Submodule.Quotient.mk ⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩,
      (mem_ramLine ρ I m0 _).2 ⟨⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩, fun g hg => by
        show fn _ _ g ∈ _
        simp only [fn, hI1 g hg, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m0), rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨b, m⟩ ⟨b', m'⟩ h
    have h1 := congrArg Subtype.val h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h1
    obtain ⟨x, hx⟩ := h1
    have hpt : ∀ g, fn (if b then 1 else 0) m g = fn (if b' then 1 else 0) m' g := by
      intro g
      have h2 := hx g
      rw [hρ g, Module.End.one_apply, sub_self] at h2
      exact sub_eq_zero.1 h2
    have hb : b = b' := by
      have h3 := hpt g2
      simp only [fn, hI1 g2 hg2I, hg2, zero_smul, zero_add, mul_one] at h3
      cases b <;> cases b' <;> simp_all
    subst hb
    have h4 := hpt g1
    simp only [fn, hg1, one_smul] at h4
    rw [add_right_cancel h4]
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hc
  exact hc
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def actM {A V J : Type} [CommRing A] [AddCommGroup V] [Module A V] (r t : A) (Y : J → V) :
    A × (J → V) →+ A × (J → V) where
  toFun u := (r * u.1, fun j => t • u.2 j + (r * u.1) • Y j)
  map_zero' := by ext <;> simp
  map_add' u v := by
    ext
    · simp [mul_add]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, smul_add, add_smul]
      abel

private def mkRep {Γ M : Type} [Group Γ] [AddCommGroup M] (n : ℕ) [Module (ZMod n) M] (T : Γ → M →+ M) (h1 : ∀ u, T 1 u = u)
    (hm : ∀ g h u, T (g * h) u = T g (T h u)) : Representation (ZMod n) Γ M where
  toFun g := ((T g).toZModLinearMap n : Module.End (ZMod n) M)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hm g h)

private theorem continuous_of_right_invariant_on_nhds_one {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (U : Set Γ) (hU : U ∈ nhds (1 : Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ U, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht hU] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.Gys.extRep :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → (∀ i, IsLocallyConstant fun g => a (Φ.χ i g)) → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod (l ^ 1)) M) (_ : Finite M) (_ : TopologicalSpace M) (_ : DiscreteTopology M) (ρ : Representation (ZMod (l ^ 1)) Γ M)
        (p : M →+ k) (q : J → M →+ k) (m0 : M), ContAction ρ ∧ (∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ρ g = 1) ∧
        (∀ g u, p (ρ g u) = a (Φ.rt w g) * p u) ∧ (∀ j g u, q j (ρ g u) = a (Φ.rt (w + w') g) * q j u + y j g * a (Φ.rt w g) * p u) ∧
        m0 ≠ 0 ∧ ∀ u ∈ Submodule.span (ZMod (l ^ 1)) {m0}, u ≠ 0 → p u ≠ 0 := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ ha hχ w w' J _ y hy
  classical
  have hlp : (l ^ 1 : ℕ) = l := pow_one l
  have hA : ∀ (v : ℤ × ℤ) g, a ↑(Φ.rt v g) =
      (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹) ^ v.1 * (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹) ^ v.2 := by
    intro v g
    have e : ∀ u : Oˣ, a ↑u = ((Units.map a.toMonoidHom u : kˣ) : k) := fun u => rfl
    rw [e, e, e, e]
    simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_zpow, map_inv, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  have hsplit : ∀ g, a ↑(Φ.rt (w + w') g) = a ↑(Φ.rt w g) * a ↑(Φ.rt w' g) := by
    intro g
    rw [hA, hA, hA]
    simp only [Prod.fst_add, Prod.snd_add]
    have h0 : a ↑(Φ.χ 0 g) ≠ 0 := ((Φ.χ 0 g).isUnit.map a).ne_zero
    have h1 : a ↑(Φ.χ 1 g) ≠ 0 := ((Φ.χ 1 g).isUnit.map a).ne_zero
    have h2 : a ↑(Φ.χ 2 g) ≠ 0 := ((Φ.χ 2 g).isUnit.map a).ne_zero
    have n1 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h1)
    have n2 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h2)
    rw [zpow_add₀ n1, zpow_add₀ n2]
    ring
  have hy1 : ∀ j, y j 1 = 0 := by
    intro j
    have := (hy j).coc 1 1
    simp only [mul_one, map_one, Units.val_one] at this
    linear_combination -this
  have hY : (⋃ j, Set.range (y j)).Finite := Set.finite_iUnion fun j => (hy j).lc.range_finite
  let A : Subring k := a.range
  haveI : Finite A := Set.Finite.to_subtype (s := (a.range : Set k)) (by rw [RingHom.coe_range]; exact ha)
  let V : Submodule A k := Submodule.span A (⋃ j, Set.range (y j))
  haveI : Module.Finite A V := Module.Finite.span_of_finite A hY
  haveI : Finite V := Module.finite_of_finite A
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hchar : ∀ x : k, (l ^ 1) • x = 0 := by
    intro x
    rw [nsmul_eq_mul, hlp, CharP.cast_eq_zero, zero_mul]
  letI iM : Module (ZMod (l ^ 1)) (A × (J → V)) := AddCommGroup.zmodModule (fun x => by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change (((l ^ 1) • x.1 : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _
    · funext j
      apply Subtype.ext
      change (((l ^ 1) • x.2 j : V) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _)
  letI : TopologicalSpace (A × (J → V)) := ⊥
  haveI : DiscreteTopology (A × (J → V)) := ⟨rfl⟩
  let rr : Γ → A := fun g => ⟨a ↑(Φ.rt w g), a.mem_range_self _⟩
  let tt : Γ → A := fun g => ⟨a ↑(Φ.rt (w + w') g), a.mem_range_self _⟩
  let YY : Γ → J → V := fun g j => ⟨y j g, Submodule.subset_span (Set.mem_iUnion.2 ⟨j, g, rfl⟩)⟩
  let T : Γ → (A × (J → V)) →+ (A × (J → V)) := fun g => actM (rr g) (tt g) (YY g)
  have cs : ∀ (c : A) (v : V), ((c • v : V) : k) = (c : k) * (v : k) := fun c v => rfl
  have h1 : ∀ u, T 1 u = u := by
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w 1) * (u.1 : k) = u.1
      simp
    · funext j
      apply Subtype.ext
      show ((tt 1 • u.2 j + (rr 1 * u.1) • YY 1 j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') 1) * (u.2 j : k) + (a ↑(Φ.rt w 1) * (u.1 : k)) * y j 1 = u.2 j
      simp [hy1]
  have hm : ∀ g h u, T (g * h) u = T g (T h u) := by
    intro g h u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w (g * h)) * (u.1 : k) = a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))
      rw [map_mul, Units.val_mul, map_mul, mul_assoc]
    · funext j
      apply Subtype.ext
      show ((tt (g * h) • u.2 j + (rr (g * h) * u.1) • YY (g * h) j : V) : k) =
        ((tt g • (tt h • u.2 j + (rr h * u.1) • YY h j) + (rr g * (rr h * u.1)) • YY g j : V) : k)
      rw [Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') (g * h)) * (u.2 j : k) + (a ↑(Φ.rt w (g * h)) * (u.1 : k)) * y j (g * h) =
        a ↑(Φ.rt (w + w') g) * (a ↑(Φ.rt (w + w') h) * (u.2 j : k) + (a ↑(Φ.rt w h) * (u.1 : k)) * y j h) +
          (a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))) * y j g
      rw [(hy j).coc g h, map_mul (Φ.rt (w + w')), map_mul (Φ.rt w), Units.val_mul, Units.val_mul,
        map_mul a, map_mul a, hsplit g, hsplit h]
      ring
  let ρ : Representation (ZMod (l ^ 1)) Γ (A × (J → V)) := mkRep (l ^ 1) T h1 hm
  have hker : ∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ∀ u, T g u = u := by
    intro g hg hyg
    have hr : ∀ v : ℤ × ℤ, a ↑(Φ.rt v g) = 1 := by
      intro v
      rw [hA, hg 0, hg 1, hg 2]
      simp
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w g) * (u.1 : k) = u.1
      rw [hr, one_mul]
    · funext j
      apply Subtype.ext
      show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = u.2 j
      rw [hr, hr, hyg]
      ring
  let p : (A × (J → V)) →+ k :=
    { toFun := fun u => (u.1 : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : J → (A × (J → V)) →+ k := fun j =>
    { toFun := fun u => (u.2 j : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let m0 : A × (J → V) := (1, 0)
  refine ⟨A × (J → V), inferInstance, iM, inferInstance, ⊥, ⟨rfl⟩, ρ, p, q, m0, ?_, fun g hg hyg => LinearMap.ext (hker g hg hyg), ?_, ?_, ?_, ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    let U : Set Γ := (⋂ i, (fun g => a (Φ.χ i g)) ⁻¹' {1}) ∩ ⋂ j, y j ⁻¹' {0}
    have hU : U ∈ nhds (1 : Γ) := by
      apply IsOpen.mem_nhds
      · exact (isOpen_iInter_of_finite fun i => (hχ i).isOpen_fiber 1).inter
          (isOpen_iInter_of_finite fun j => (hy j).lc.isOpen_fiber 0)
      · refine ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun j => ?_⟩
        · simp
        · exact hy1 j
    apply continuous_of_right_invariant_on_nhds_one U hU
    intro g h hh
    have hh1 : ∀ i, a (Φ.χ i h) = 1 := fun i => Set.mem_iInter.1 hh.1 i
    have hh2 : ∀ j, y j h = 0 := fun j => Set.mem_iInter.1 hh.2 j
    show T (g * h) m = T g m
    rw [hm, hker h hh1 hh2 m]
  · intro g u
    rfl
  · intro j g u
    show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = _
    rw [Submodule.coe_add, cs, cs]
    show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g =
      a ↑(Φ.rt (w + w') g) * (u.2 j : k) + y j g * a ↑(Φ.rt w g) * (u.1 : k)
    ring
  · intro h
    have := congrArg (fun u : A × (J → V) => (u.1 : k)) h
    simp [m0] at this
  · intro u hu hne
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hne ⊢
    intro hp
    apply hne
    rw [map_nsmul] at hp
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change ((c.val • (1 : A) : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hp
    · funext j
      apply Subtype.ext
      change ((c.val • (0 : V) : V) : k) = 0
      rw [smul_zero]
      rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rt_val {O Γ k : Type} [CommRing O] [Group Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (w : ℤ × ℤ) (g : Γ) :
    a (Φ.rt w g) = (a (Φ.χ 0 g) * (a (Φ.χ 1 g))⁻¹) ^ w.1 * (a (Φ.χ 0 g) * (a (Φ.χ 2 g))⁻¹) ^ w.2 := by
  have h : ∀ u : Oˣ, a (u : O) = ((Units.map (a : O →* k) u : kˣ) : k) := fun _ => rfl
  have e : Φ.rt w g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ w.1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ w.2 := rfl
  rw [e, h, h (Φ.χ 0 g), h (Φ.χ 1 g), h (Φ.χ 2 g)]
  simp only [map_mul, map_zpow, map_inv, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]

private theorem rt_lc {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) : IsLocallyConstant fun g => a (Φ.rt w g) := by
  simp only [rt_val]
  exact (((h.lc 0).mul ((h.lc 1).comp (·⁻¹))).comp (· ^ w.1)).mul (((h.lc 0).mul ((h.lc 2).comp (·⁻¹))).comp (· ^ w.2))

private theorem rt_kill {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) (g : Γ) (hg : g ∈ Φ.N) : a (Φ.rt w g) = 1 := by
  simp [rt_val, h.kill g hg]

theorem UpperTheory.V.Ws.Gys.cupNorm :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → ∀ (w w' : ℤ × ℤ), a (Φ.rt w Φ.g0) ≠ 1 → a (Φ.rt (w + w') Φ.g0) ≠ 1 → ∀ (J : Type) (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j) ∧ y j Φ.g0 = 0) →
      ∀ (x : Γ → k) (m : Φ.ι → k), Φ.Coc a w x → Φ.LocTriv a w x m → (∀ j, ∃ z, Φ.Cup a w w' x (y j) z m) →
        ∃ (x' : Γ → k) (m' : Φ.ι → k), Φ.Coc a w x' ∧ x' Φ.g0 = 0 ∧ Φ.LocTriv a w x' m' ∧ (∀ g, a (Φ.rt w g) = 1 → x' g = x g) ∧
          ∀ j, ∃ z, Φ.Cup a w w' x' (y j) z m' ∧ z Φ.g0 = 0 := by
  intro O Γ k _ _ _ _ Φ a hok w w' h1 h2 J y hy x m hx hm hz
  have n1 : 1 - a (Φ.rt w Φ.g0) ≠ 0 := sub_ne_zero.2 h1.symm
  have n2 : 1 - a (Φ.rt (w + w') Φ.g0) ≠ 0 := sub_ne_zero.2 h2.symm
  have hmul : ∀ (u : ℤ × ℤ) (g h : Γ), a (Φ.rt u (g * h)) = a (Φ.rt u g) * a (Φ.rt u h) := fun u g h => by
    rw [map_mul, Units.val_mul, map_mul]
  have hadd : ∀ g : Γ, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  obtain ⟨m1, hm1⟩ : ∃ m1 : k, x Φ.g0 = m1 - a (Φ.rt w Φ.g0) * m1 :=
    ⟨x Φ.g0 / (1 - a (Φ.rt w Φ.g0)), by field_simp⟩
  have c := fun t : k => (IsLocallyConstant.const t : IsLocallyConstant fun _ : Γ => t)
  refine ⟨fun g => x g - (m1 - a (Φ.rt w g) * m1), fun v => m v - m1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j => ?_⟩
  · exact hx.lc.sub ((c m1).sub ((rt_lc Φ a hok w).mul (c m1)))
  · intro g h
    rw [hx.coc, hmul]; ring
  · intro g hg
    rw [hx.kill g hg, rt_kill Φ a hok w g hg]; ring
  · exact sub_eq_zero.2 hm1
  · intro v s hs
    beta_reduce
    rw [hm v s hs]; ring
  · intro g hg
    beta_reduce
    rw [hg]; ring
  · obtain ⟨z, hz⟩ := hz j
    obtain ⟨hyj, hy0⟩ := hy j
    obtain ⟨o1, ho1⟩ : ∃ o1 : k, z Φ.g0 = o1 - a (Φ.rt (w + w') Φ.g0) * o1 :=
      ⟨z Φ.g0 / (1 - a (Φ.rt (w + w') Φ.g0)), by field_simp⟩
    refine ⟨fun g => z g - (o1 - a (Φ.rt (w + w') g) * o1 - y j g * a (Φ.rt w g) * m1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hz.lc.sub (((c o1).sub ((rt_lc Φ a hok _).mul (c o1))).sub ((hyj.lc.mul (rt_lc Φ a hok w)).mul (c m1)))
    · intro g h
      rw [hz.coc, hyj.coc, hmul, hmul, hadd g, hadd h]; ring
    · intro g hg
      rw [hz.kill g hg, hyj.kill g hg, rt_kill Φ a hok _ g hg]; ring
    · intro v
      obtain ⟨o, ho⟩ := hz.loc v
      refine ⟨o - o1, fun s hs => ?_⟩
      rw [ho s hs]; ring
    · beta_reduce
      rw [ho1, hy0]; ring
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.dataAl :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nM p.r →
      ∃ x : Γ → R, Φ.Coc a (-wAl) x ∧ x Φ.g0 = 0 ∧ Φ.LocTriv a (-wAl) x (fun v => p.n v 1 0) ∧ ∀ g, p.r g 1 0 = x g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hp hs
  have h12 : ∀ g, p.r g 1 2 = 0 := fun g => hs g 1 2 (by decide) (by decide)
  have h13 : ∀ g, p.r g 1 3 = 0 := fun g => hs g 1 3 (by decide) (by decide)
  have hd := hp.res.diag
  have hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_mul, ← Units.val_mul]
    congr 2
    simp [Fr.rt, wAl]
  have hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => by
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]
  refine ⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (hlc 1 0).mul ?_
    have e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0 := by
      funext g
      simp only [Function.comp, hd]
      exact (Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm
    rw [e]
    exact (hlc 0 0).comp _
  · intro g h
    have e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0 := by
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]; ring
    rw [e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]
    linear_combination (p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h
  · intro g hg
    simp [hp.pair.kill g hg]
  · have : p.r Φ.g0 1 0 = 0 := hp.pair.nrm (by decide)
    simp [this]
  · intro v s hsv
    obtain ⟨l1, l2, l3⟩ := hp.pair.low v
    have hinv : p.n v * adj (p.n v) = 1 := by
      rw [IsGSp, one_smul] at l1
      exact mul_eq_one_comm.mp l1
    have hU := hp.pair.flag v s hsv
    have hc := hp.res.char v s hsv 0
    unfold PD.ψ at hc
    have key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    generalize adj (p.n v) * p.r s * p.n v = U at hU hc key
    have k := congrFun (congrFun key 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide),
      hU 3 0 (by decide), hc, h12, h13, hd, l2, l2] at k
    rw [hrt]
    beta_reduce
    linear_combination (-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s
  · intro g
    beta_reduce
    rw [mul_assoc, hu, mul_one]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_of_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {f : Γ → R} (h : UpperTheory.V.Alg.AdicCont ⊥ f) :
    IsLocallyConstant f := by
  refine IsLocallyConstant.desc _ _ (h 1) ?_
  intro x y hxy
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

theorem UpperTheory.V.Ws.Gys.dataPs :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nP p.r →
      ∃ y : Γ → R, Φ.Coc a (-wPs) y ∧ y Φ.g0 = 0 ∧ Φ.LocTriv a (-wPs) y (fun v => p.n v 2 0) ∧ ∀ g, p.r g 2 0 = y g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hR hS
  have hc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => lc_of_cont (hR.cont i j)
  have hd := hR.res.diag
  have hinv : ∀ g, Ring.inverse (p.r g 0 0) = a ↑((Φ.χ 0 g)⁻¹) := by
    intro g
    rw [hd g 0]
    have hu : a ↑(Φ.χ 0 g) = ↑(Units.map a.toMonoidHom (Φ.χ 0 g)) := rfl
    rw [hu, Ring.inverse_unit]
    rfl
  have hone : ∀ g, a ↑(Φ.χ 0 g) * a ↑((Φ.χ 0 g)⁻¹) = 1 := by
    intro g
    rw [← map_mul, Units.mul_inv, map_one]
  have he : ∀ g, Φ.rt (-wPs) g = Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    intro g
    simp [Fr.rt, wPs]
  refine ⟨fun g => p.r g 2 0 * Ring.inverse (p.r g 0 0), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hc 2 0).mul ((hc 0 0).comp Ring.inverse)
  · intro g h
    have z1 : p.r g 2 1 = 0 := hS g 2 1 (by decide) (by decide)
    have z3 : p.r g 2 3 = 0 := hS g 2 3 (by decide) (by decide)
    show p.r (g * h) 2 0 * Ring.inverse (p.r (g * h) 0 0) =
      p.r g 2 0 * Ring.inverse (p.r g 0 0) + a ↑(Φ.rt (-wPs) g) * (p.r h 2 0 * Ring.inverse (p.r h 0 0))
    rw [hinv (g * h), hinv g, hinv h, he g]
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z1, z3, zero_mul, add_zero, hd, mul_inv,
      Units.val_mul]
    linear_combination (p.r g 2 0 * a ↑((Φ.χ 0 g)⁻¹)) * hone h
  · intro g hg
    show p.r g 2 0 * Ring.inverse (p.r g 0 0) = 0
    rw [hR.pair.kill g hg, Matrix.one_apply_ne (by decide), zero_mul]
  · show p.r Φ.g0 2 0 * Ring.inverse (p.r Φ.g0 0 0) = 0
    rw [hR.pair.nrm (by decide : (2 : Fin 4) ≠ 0), zero_mul]
  · intro v s hs
    have hn := hR.pair.low v
    have hna0 : adj (p.n v) * p.n v = 1 := by
      have h1 := hn.1
      simpa [IsGSp] using h1
    have hna : p.n v * adj (p.n v) = 1 := mul_eq_one_comm.mp hna0
    have hX := hR.pair.flag v s hs
    have hch : (adj (p.n v) * p.r s * p.n v) 0 0 = a ↑(Φ.χ 0 s) := hR.res.char v s hs 0
    have key : p.r s * p.n v = p.n v * (adj (p.n v) * p.r s * p.n v) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hna, Matrix.one_mul]
    have k20 := congrFun (congrFun key 2) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at k20
    rw [hS s 2 1 (by decide) (by decide), hS s 2 3 (by decide) (by decide), hd s 2, hn.2.1 0,
      hX 1 0 (by decide), hX 2 0 (by decide), hX 3 0 (by decide), hch] at k20
    show p.r s 2 0 * Ring.inverse (p.r s 0 0) = p.n v 2 0 - a ↑(Φ.rt (-wPs) s) * p.n v 2 0
    rw [hinv, he s, Units.val_mul, map_mul]
    linear_combination (a ↑((Φ.χ 0 s)⁻¹)) * k20 + (p.n v 2 0) * hone s
  · intro g
    show p.r g 2 0 = p.r g 2 0 * Ring.inverse (p.r g 0 0) * a ↑(Φ.χ 0 g)
    rw [hinv]
    linear_combination (-(p.r g 2 0)) * hone g
end
