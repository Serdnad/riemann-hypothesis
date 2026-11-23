module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

private theorem reps_setoid {G : Type} (r : Setoid G) (Y : Finset G) (x₀ : G)
    (hY : ∀ g, ∃ y ∈ Y, r y g) :
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j, r (x i) (x j) → i = j) ∧ ∀ g, ∃ i, r (x i) g := by
  classical
  have hσ : ∀ q : Quotient r, ∃ y ∈ Y, Quotient.mk r y = q := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨y, hy, h⟩ := hY g
      exact ⟨y, hy, Quotient.sound h⟩
  choose σ hσY hσ using hσ
  haveI : Finite (Quotient r) := by
    refine Finite.of_injective (fun q => (⟨σ q, hσY q⟩ : Y)) ?_
    intro a b h
    have h' : σ a = σ b := congrArg Subtype.val h
    rw [← hσ a, ← hσ b, h']
  haveI : Nonempty (Quotient r) := ⟨Quotient.mk r x₀⟩
  obtain ⟨n, hn⟩ : ∃ n, Nat.card (Quotient r) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := Quotient r)).ne'
  let e₀ : Fin (n + 1) ≃ Quotient r := (Finite.equivFinOfCardEq hn).symm
  let e : Fin (n + 1) ≃ Quotient r := e₀.trans (Equiv.swap (e₀ 0) (Quotient.mk r x₀))
  have he : e 0 = Quotient.mk r x₀ := by simp [e]
  let x : Fin (n + 1) → G := fun i => if i = 0 then x₀ else σ (e i)
  have hx : ∀ i, Quotient.mk r (x i) = e i := by
    intro i
    by_cases h : i = 0
    · subst h; simp [x, he]
    · simp [x, h, hσ]
  refine ⟨n, x, by simp [x], ?_, ?_, ?_⟩
  · intro i
    by_cases h : i = 0
    · left; simp [x, h]
    · right; simp [x, h, hσY]
  · intro i j h
    apply e.injective
    rw [← hx, ← hx]
    exact Quotient.sound h
  · intro g
    refine ⟨e.symm (Quotient.mk r g), Quotient.exact ?_⟩
    rw [hx]; simp

theorem UpperTheory.orbitalFiber_representatives :
    UpperTheory.V.Z.Sym.Glob.Fib.Reps := by
  intro Γ G _ _ ι S U' Y x₀ hS hY
  let r : Setoid G :=
    { r := fun a b => ∃ γ, ∃ s ∈ S, ∃ u ∈ U', b = ι γ * s * a * u
      iseqv :=
        { refl := fun a => ⟨1, 1, S.one_mem, 1, U'.one_mem, by simp⟩
          symm := by
            rintro a b ⟨γ, s, hs, u, hu, rfl⟩
            refine ⟨γ⁻¹, ι γ * s⁻¹ * (ι γ)⁻¹, hS.conj_mem _ (S.inv_mem hs) _, u⁻¹, U'.inv_mem hu, ?_⟩
            rw [map_inv]; group
          trans := by
            rintro a b c ⟨γ, s, hs, u, hu, rfl⟩ ⟨γ', s', hs', u', hu', rfl⟩
            refine ⟨γ' * γ, (ι γ)⁻¹ * s' * (ι γ)⁻¹⁻¹ * s,
              S.mul_mem (hS.conj_mem _ hs' _) hs, u * u', U'.mul_mem hu hu', ?_⟩
            rw [map_mul]; group } }
  obtain ⟨n, x, h0, h1, h2, h3⟩ := reps_setoid r Y x₀ (by
    intro g
    obtain ⟨γ, s, hs, y, hy, u, hu, h⟩ := hY g
    exact ⟨y, hy, γ, s, hs, u, hu, h⟩)
  refine ⟨n, x, h0, h1, fun i j γ s hs u hu h => h2 i j ⟨γ, s, hs, u, hu, h⟩, fun g => ?_⟩
  obtain ⟨i, γ, s, hs, u, hu, h⟩ := h3 g
  exact ⟨i, γ, s, hs, u, hu, h⟩
end

section

theorem UpperTheory.orbitalFiber_card_formula : UpperTheory.V.Z.Sym.Glob.Fib.CardFib := by
  intro G _ S U U' x Ux s₀ hS hU hx
  classical
  have hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S := by
    intro w
    have h1 := S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)
    simpa [mul_assoc] using h1
  let g : ↥(U' ⊓ S) → ↥S ⧸ Ux := fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)
  have hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U := by
    intro w w'
    simp only [g]
    rw [QuotientGroup.eq, hx]
    have e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
  have hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} := by
    intro w
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)
    simp only [Set.mem_setOf_eq, g]
    rw [hk, QuotientGroup.eq]
    have hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U' := hU ((hx k).1 k.2)
    have e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) =
        (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)
  rw [← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) →
      {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} :=
    Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by
      have h := QuotientGroup.leftRel_apply.1 hab
      simpa [Subgroup.mem_subgroupOf] using h)))
  refine (Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg Subtype.val hab
    change g a = g b at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (hg a b).1 h
  · rintro ⟨s, hs⟩
    rw [Set.mem_setOf_eq] at hs
    have hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S := by
      simpa using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹
    have hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U' := by
      have h1 := QuotientGroup.eq.1 hs
      have e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x =
          ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹ := by
        group
      rw [e]
      exact U'.inv_mem h1
    refine ⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)),
      Subtype.ext ?_⟩
    change g _ = s
    conv_rhs => rw [← QuotientGroup.out_eq' s]
    simp only [g]
    congr 1
    apply Subtype.ext
    dsimp only
    group
end

section

open MulAction

theorem UpperTheory.orbitalFiber_pushforward_eq_zero :
    UpperTheory.V.Z.Sym.Glob.Fib.PushZero := by
  intro H Y _ _ H₀ k hidx htriv hk hfin
  classical
  have hout : ∀ (o : orbitRel.Quotient H Y) (y : Y),
      (Quotient.mk (orbitRel H Y) y : orbitRel.Quotient H Y) = o ↔ y ∈ orbit H o.out := by
    intro o y
    rw [← orbitRel_apply, ← Quotient.eq (r := orbitRel H Y), Quotient.out_eq]
  have hkeq : ∀ (x y : Y), y ∈ orbit H x → k y = k x := by
    rintro x y ⟨h, rfl⟩
    exact hk h x
  set S : Finset Y := hfin.toFinset with hS
  have hmem : ∀ y, y ∈ S ↔ k y ≠ 0 := by
    intro y; simp [hS]
  let q : Y → orbitRel.Quotient H Y := fun y => Quotient.mk (orbitRel H Y) y
  have h1 : ∑ᶠ y, k y = ∑ y ∈ S, k y := finsum_eq_sum k hfin
  have h2 : UpperTheory.V.Z.Sym.gq H₀ k =
      ∑ o ∈ S.image q, k o.out / (H₀.relIndex (stabilizer H o.out) : ℂ) := by
    unfold UpperTheory.V.Z.Sym.gq
    apply finsum_eq_sum_of_support_subset
    intro o ho
    have hne : k o.out ≠ 0 := by
      intro h0
      exact ho (by simp [h0])
    simp only [Finset.coe_image]
    exact ⟨o.out, by simpa [hmem] using hne, Quotient.out_eq o⟩
  rw [h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image q) (g := q)
    (fun y hy => Finset.mem_image_of_mem q hy), Finset.sum_div]
  refine Finset.sum_congr rfl fun o ho => ?_
  obtain ⟨y₀, hy₀, hy₀o⟩ := Finset.mem_image.mp ho
  have hne : k o.out ≠ 0 := by
    rw [← hkeq o.out y₀ ((hout o y₀).mp hy₀o)]
    exact (hmem y₀).mp hy₀
  have hset : ((S.filter fun y => q y = o : Finset Y) : Set Y) = orbit H o.out := by
    ext y
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · exact fun h => (hout o y).mp h.2
    · intro h
      exact ⟨(hmem y).mpr (by rw [hkeq _ _ h]; exact hne), (hout o y).mpr h⟩
  have hcard : (S.filter fun y => q y = o).card = (stabilizer H o.out).index := by
    rw [index_stabilizer, ← hset, Set.ncard_coe_finset]
  have hle : H₀ ≤ stabilizer H o.out := fun z hz => htriv z hz _
  have hmul := Subgroup.relIndex_mul_index hle
  have hsum : ∑ y ∈ S with q y = o, k y = ((stabilizer H o.out).index : ℂ) * k o.out := by
    rw [Finset.sum_congr rfl (g := fun _ => k o.out), Finset.sum_const, hcard, nsmul_eq_mul]
    intro y hy
    exact hkeq _ _ ((hout o y).mp (Finset.mem_filter.mp hy).2)
  rw [← hmul] at hidx
  have ha : ((H₀.relIndex (stabilizer H o.out) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (left_ne_zero_of_mul hidx)
  have hb : (((stabilizer H o.out).index : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (right_ne_zero_of_mul hidx)
  rw [hsum, ← hmul, Nat.cast_mul]
  field_simp
end

section

open MeasureTheory in
theorem UpperTheory.exists_nondegenerate_right_invariant_form_of_compact_quotient :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ] (C : Set G), IsCompact C → (∀ g, ∃ γ ∈ Γ, ∃ c ∈ C, g = γ * c) → ∃ B : (G → ℂ) →ₗ⋆[ℂ] (G → ℂ) →ₗ[ℂ] ℂ, (∀ φ : G → ℂ, Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → B φ φ = 0 → φ = 0) ∧ ∀ (x : G) (φ ψ : G → ℂ), Continuous φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) → B (fun g => φ (g * x)) (fun g => ψ (g * x)) = B φ ψ := by
  intro G _ _ _ _ _ _ Γ _ C hC hcov
  classical
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure G, μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨𝓕, -, h𝓕'⟩ := Formalism.IndefR.Eqv.G5.fdom_exists_all Γ
  have h𝓕 := h𝓕' μ
  have hfin : μ 𝓕 < ⊤ := by
    refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro g hg
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hg⟩
  obtain ⟨-, hR, -⟩ := GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G Γ μ 𝓕 h𝓕 hfin
  have hright : ∀ (y : G) (u : G → ℂ), (∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) →
      ∫ h in 𝓕, u (h * y) ∂μ = ∫ h in 𝓕, u h ∂μ := by
    intro y u hu
    have h' : IsFundamentalDomain Γ ((fun h => h * y) '' 𝓕) μ := by
      refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
      · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
      · intro γ h
        exact mul_assoc (γ : G) h y
    rw [h𝓕.setIntegral_eq h' (f := u) (fun γ h => hu γ γ.2 h)]
    exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
      (measurableEmbedding_mulRight y) u 𝓕).symm
  let N : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g =>
        congrArg₂ (· + ·) (ha.2 γ hγ g) (hb.2 γ hγ g)⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g =>
        congrArg (c • ·) (ha.2 γ hγ g)⟩ }
  have hRN : ∀ k : G, ∀ φ ∈ N, (fun g => φ (g * k)) ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x g) * y g) 𝓕 μ := by
    intro x hx y hy
    have hc : Continuous (fun g => star (x g) * y g) := hx.1.star.mul hy.1
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    rw [hx.2 γ hγ, hy.2 γ hγ]
    exact hM c hc
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (G → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : G → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : G → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (G → ℂ) → (G → ℂ) → ℂ := fun x y => ∫ g in 𝓕, star ((P x).1 g) * (P y).1 g ∂μ
  let B : (G → ℂ) →ₗ⋆[ℂ] (G → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, mul_assoc])
    (fun x y y' => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      exact mul_left_comm (star ((P x).1 g)) c ((P y).1 g))
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x g) * y g ∂μ := by
    intro x hx y hy
    change (∫ g in 𝓕, star ((P x).1 g) * (P y).1 g ∂μ) = _
    rw [hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT1 hT2 h0
    have hT : T ∈ N := ⟨hT1, hT2⟩
    rw [hB _ hT _ hT] at h0
    have hre : ∫ g in 𝓕, star (T g) * T g ∂μ = ((∫ g in 𝓕, ‖T g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [hre, Complex.ofReal_eq_zero] at h0
    have hi : IntegrableOn (fun g => ‖T g‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T g) * T g‖) = fun g => ‖T g‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => sq_nonneg ‖T g‖) hi).1 h0
    exact funext (GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant Γ μ 𝓕 h𝓕
      T hT1 hT2 (hae.mono fun g hg => norm_eq_zero.mp (sq_eq_zero_iff.mp hg)))
  · intro k T T' h1 h2 h3 h4
    have hT : T ∈ N := ⟨h1, h2⟩
    have hT' : T' ∈ N := ⟨h3, h4⟩
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    exact hright k (fun g => star (T g) * T' g) (fun γ hγ g => by simp only [h2 γ hγ, h4 γ hγ])
end
