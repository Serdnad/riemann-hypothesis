module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
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

@[expose] public section

section

open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

private theorem card_ker_range {A X Y : Type} [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (f : X →ₗ[A] Y) : Nat.card X = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private theorem inj_of {A X Y Z : Type} [CommRing A] [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] [AddCommGroup Z] [Module A Z] (q : X →ₗ[A] Y) (b : X →ₗ[A] Z) (K : Submodule A Z)
    (h1 : ∀ x, q x = 0 → b x = 0) (h2 : ∀ z ∈ K, ∃ x, b x = z) :
    ∃ f : K → Y, Function.Injective f := by
  choose s hs using h2
  refine ⟨fun z => q (s z.1 z.2), fun z z' hzz => ?_⟩
  have h := h1 (s z.1 z.2 - s z'.1 z'.2) (by rw [map_sub]; exact sub_eq_zero.2 hzz)
  rw [map_sub, hs, hs, sub_eq_zero] at h
  exact Subtype.ext h

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)

private abbrev Tq : Type := ∀ w, H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)

private def aMap : H1 D.M.ρ →ₗ[A] Tq D :=
  LinearMap.pi fun w => (H1ur (D.Q w).ρ (P.J w)).mkQ.comp (D.loc1 w)

private theorem ker_aMap : LinearMap.ker (aMap D) = D.Sel := by
  ext c
  simp only [LinearMap.mem_ker, Dat.Sel, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h w
    have := congrFun h w
    simpa [aMap, Submodule.Quotient.mk_eq_zero] using this
  · intro h
    funext w
    simp [aMap, h w]

private def qMap : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] Tq D ⧸ LinearMap.range (aMap D) :=
  (LinearMap.range (aMap D)).mkQ.comp (LinearMap.pi fun w =>
    (H1ur (D.Q w).ρ (P.J w)).mkQ.comp ((Submodule.mkQ _).comp (LinearMap.proj w)))

private def bZ : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] D.selmerSecondCocycles where
  toFun y := ⟨(0, fun w => (y w).1), zero_mem _, fun w => ⟨(y w).2.1, fun g h => by
    simp [(y w).2.2]⟩⟩
  map_add' y y' := by ext <;> simp
  map_smul' c y := by ext <;> simp

private def bMap : (∀ w, Z1 (D.Q w).ρ) →ₗ[A] D.H2LocalConditions := (Submodule.mkQ _).comp (bZ D)

private def cZ : D.selmerSecondCocycles →ₗ[A] Z2 D.M.ρ where
  toFun p := ⟨p.1.1, p.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def cMap : D.H2LocalConditions →ₗ[A] H2 D.M.ρ :=
  Submodule.mapQ _ _ (cZ D) (by
    rintro p ⟨x, a1, a2, -⟩
    exact ⟨x, a1, a2.symm⟩)

private theorem range_cMap : LinearMap.range (cMap D) ≤ LinearMap.ker D.loc2 := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker]
  funext w
  simp only [cMap, Dat.loc2, LinearMap.pi_apply, compatiblePairH2, Submodule.mapQ_apply, Pi.zero_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem]
  refine ⟨p.1.2 w, (p.2.2 w).1, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  exact ((p.2.2 w).2 g h).symm

private theorem ker_qMap (y : ∀ w, Z1 (D.Q w).ρ) (hy : qMap D y = 0) : bMap D y = 0 := by
  simp only [qMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨c, hc⟩ := hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hw : ∀ w, ∃ Y, ∀ g ∈ P.J w, (y w).1 g - D.π w (x.1 (P.φ w g)) = (D.Q w).ρ g Y - Y := by
    intro w
    have e := congrFun hc w
    simp only [aMap, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.proj_apply, Dat.loc1, pairH1DecompositionMap, Submodule.mapQ_apply] at e
    rw [Submodule.Quotient.eq, ← Submodule.Quotient.mk_sub, H1ur, LinearMap.mem_ker] at e
    simp only [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at e
    obtain ⟨m, hm⟩ := e
    refine ⟨-m, fun g hg => ?_⟩
    have h3 := hm ⟨g, hg⟩
    change D.π w (x.1 (P.φ w g)) - (y w).1 g = (D.Q w).ρ g m - m at h3
    rw [map_neg, ← neg_sub (D.π w (x.1 (P.φ w g))) ((y w).1 g), h3]
    abel
  choose Y hY using hw
  simp only [bMap, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  refine ⟨x.1, x.2.1, ?_, fun w => ⟨sub_mem (y w).2
    (compatiblePairCocycles1 D.M.ρ (D.Q w).ρ (P.φ w) (P.cont w) (D.π w) continuous_of_discreteTopology (D.equiv w) x).2,
    Y w, hY w⟩⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [d1_apply, x.2.2 g h]
  show (0 : D.M.X) = _
  abel

private theorem ker_cMap (z : D.H2LocalConditions) (hz : z ∈ LinearMap.ker (cMap D)) : ∃ y, bMap D y = z := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  simp only [cMap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, separated_dvr_second_cohomology_mem] at hz
  obtain ⟨x, hx, hdx⟩ := hz
  have hyZ : ∀ w, (p.1.2 w - fun g => D.π w (x (P.φ w g))) ∈ Z1 (D.Q w).ρ := by
    intro w
    refine ⟨(p.2.2 w).1.sub ((continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))),
      fun g h => ?_⟩
    have e' : D.π w (d1 D.M.ρ x (P.φ w g, P.φ w h)) = d1 (D.Q w).ρ (p.1.2 w) (g, h) := by
      rw [hdx]
      exact (p.2.2 w).2 g h
    rw [d1_apply, d1_apply, ← (P.φ w).map_mul g h] at e'
    simp only [map_sub, map_add (f := _), D.equiv] at e'
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero] at e' ⊢
    rw [← e']
    abel
  refine ⟨fun w => ⟨_, hyZ w⟩, ?_⟩
  simp only [bMap, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨-x, hx.neg, ?_, fun w => ?_⟩
  · rw [map_neg, hdx]
    exact zero_sub _
  · show ((p.1.2 w - fun g => D.π w (x (P.φ w g))) - p.1.2 w) - (fun g => D.π w ((-x) (P.φ w g))) ∈ D.abelian₂ w
    convert zero_mem (D.abelian₂ w) using 1
    funext g
    simp only [Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, map_neg]
    abel

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.count :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D : Dat A P) (s : ℕ) (dw e : P.ι → ℕ), 0 < s → Finite (H1 D.M.ρ) → Finite (H2 D.M.ρ) → (∀ w, Finite (H1 (D.Q w).ρ) ∧ Finite (H2 (D.Q w).ρ)) → Nat.card (H2 D.M.ρ) * s ^ (∑ w, dw w) ≤ Nat.card (H1 D.M.ρ) → (∀ w, Nat.card (H1 (D.Q w).ρ) ≤ Nat.card (H1ur (D.Q w).ρ (P.J w)) * Nat.card (H2 (D.Q w).ρ) * e w * s ^ dw w) → Finite D.H2LocalConditions ∧ Nat.card D.H2LocalConditions ≤ Nat.card D.Sel * (∏ w, e w) * Nat.card D.Ck2 := by
  intro A Γ _ _ _ _ P D s dw e hs hH1 hH2 hQ hM hW
  haveI : ∀ w, Finite (H1 (D.Q w).ρ) := fun w => (hQ w).1
  haveI : ∀ w, Finite (H2 (D.Q w).ρ) := fun w => (hQ w).2
  haveI : ∀ w, Finite (H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)) := fun w =>
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  haveI : Finite (Tq D) := Pi.finite
  haveI : Finite (Tq D ⧸ LinearMap.range (aMap D)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  obtain ⟨ψ, hψ⟩ := inj_of (qMap D) (bMap D) (LinearMap.ker (cMap D)) (ker_qMap D) (ker_cMap D)
  haveI : Finite (LinearMap.ker (cMap D)) := Finite.of_injective ψ hψ
  have hK : Nat.card (LinearMap.ker (cMap D)) ≤ Nat.card (Tq D ⧸ LinearMap.range (aMap D)) :=
    Nat.card_le_card_of_injective ψ hψ
  have hR : Nat.card (LinearMap.range (cMap D)) ≤ Nat.card (LinearMap.ker D.loc2) :=
    Nat.card_le_card_of_injective (Submodule.inclusion (range_cMap D)) (Submodule.inclusion_injective _)
  have hH := card_ker_range (cMap D)
  have hA := card_ker_range (aMap D)
  rw [ker_aMap] at hA
  have hL := card_ker_range D.loc2
  have hT := Submodule.card_eq_card_quotient_mul_card (LinearMap.range (aMap D))
  have hP : Nat.card (∀ w, H2 (D.Q w).ρ) = Nat.card (LinearMap.range D.loc2) * Nat.card D.Ck2 :=
    Submodule.card_eq_card_quotient_mul_card _
  have hTq : Nat.card (Tq D) ≤ Nat.card (∀ w, H2 (D.Q w).ρ) * (∏ w, e w) * s ^ (∑ w, dw w) := by
    show Nat.card (∀ w, H1 (D.Q w).ρ ⧸ H1ur (D.Q w).ρ (P.J w)) ≤ _
    rw [Nat.card_pi, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro w _
    have h1 := Submodule.card_eq_card_quotient_mul_card (H1ur (D.Q w).ρ (P.J w))
    have hpos : 0 < Nat.card (H1ur (D.Q w).ρ (P.J w)) := Nat.card_pos
    have h2 := hW w
    rw [h1, mul_assoc, mul_assoc] at h2
    rw [mul_assoc]
    exact Nat.le_of_mul_le_mul_left h2 hpos
  have key : ∀ a r q kl sel ra rl ck t pq E S h1 h2 nH : ℕ, nH = a * r → a ≤ q → r ≤ kl →
      h1 = sel * ra → h2 = kl * rl → t = ra * q → pq = rl * ck → t ≤ pq * E * S → h2 * S ≤ h1 →
      0 < h1 → 0 < pq → nH ≤ sel * E * ck := by
    intro a r q kl sel ra rl ck t pq E S h1 h2 nH en haq hrk e1 e2 et ep htp hhs p1 p2
    subst en e1 e2 et ep
    have hmain : a * r * ((sel * ra) * (rl * ck)) ≤ sel * E * ck * ((sel * ra) * (rl * ck)) := by
      calc a * r * ((sel * ra) * (rl * ck)) ≤ q * kl * ((sel * ra) * (rl * ck)) := by gcongr
        _ = (ra * q) * sel * (kl * rl) * ck := by ring
        _ ≤ (rl * ck * E * S) * sel * (kl * rl) * ck := by gcongr
        _ = rl * ck * E * sel * ck * (kl * rl * S) := by ring
        _ ≤ rl * ck * E * sel * ck * (sel * ra) := by gcongr
        _ = sel * E * ck * ((sel * ra) * (rl * ck)) := by ring
    exact Nat.le_of_mul_le_mul_right hmain (Nat.mul_pos p1 p2)
  have hpos : 0 < Nat.card D.H2LocalConditions := by
    rw [hH]
    exact Nat.mul_pos Nat.card_pos Nat.card_pos
  exact ⟨Nat.finite_of_card_ne_zero hpos.ne',
    key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hH hK hR hA hL hT hP hTq hM Nat.card_pos Nat.card_pos⟩
end
end

section

open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

section SlopeTestRemainingChoices

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ}

private theorem coboundary_mem_cocycles_local [IsTopologicalGroup Γ] (D : Dat A P) {b : D.C2} (hb : b ∈ D.selmerSecondCoboundaries) : b ∈ D.selmerSecondCocycles := by
  obtain ⟨x, hx, h1, h2⟩ := hb
  have hc : ∀ s t : Γ, b.1 (s, t) = D.M.ρ s (x t) - x (s * t) + x s := by
    intro s t
    rw [h1]
    exact d1_apply _ _ _ _
  refine ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · have e : b.1 = fun q : Γ × Γ => D.M.ρ q.1 (x q.2) - x (q.1 * q.2) + x q.1 := by
      funext q
      exact hc q.1 q.2
    rw [e]
    have hact : Continuous fun p : Γ × D.M.X => D.M.ρ p.1 p.2 := D.M.cont
    have h3 : Continuous fun q : Γ × Γ => D.M.ρ q.1 (x q.2) :=
      hact.comp (continuous_fst.prodMk (hx.comp continuous_snd))
    exact (h3.sub (hx.comp continuous_mul)).add (hx.comp continuous_fst)
  · intro g h k
    rw [hc, hc, hc, hc]
    simp only [map_sub, map_add (f := _), map_mul, Module.End.mul_apply, mul_assoc]
    abel
  · have hF : Continuous fun g : P.G w => D.π w (x (P.φ w g)) :=
      (continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))
    have hy := (h2 w).1.1
    have := hy.add hF
    simpa using this
  · intro g h
    have hyg := (h2 w).1.2 g h
    simp only [Pi.sub_apply, map_sub] at hyg
    have e : b.2 w (g * h) = b.2 w g - D.π w (x (P.φ w g)) + ((D.Q w).ρ g (b.2 w h)
        - (D.Q w).ρ g (D.π w (x (P.φ w h)))) + D.π w (x (P.φ w (g * h))) := by
      rw [← sub_eq_zero] at hyg ⊢
      rw [← hyg]
      abel
    rw [hc, d1_apply, e, ← (P.φ w).map_mul g h]
    simp only [map_sub, map_add (f := _), D.equiv]
    abel

private theorem coboundary_lift_local_conditions {D D'' : Dat A P} (g : D.Hom D'') (hs : Function.Surjective g.f)
    (hl : ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s)
    {q : D''.C2} (hq : q ∈ D''.selmerSecondCoboundaries) : ∃ b ∈ D.selmerSecondCoboundaries, g.c2 b = q := by
  obtain ⟨x'', hx'', h1, h2⟩ := hq
  choose s hs' using hs
  have hl' := fun w => hl w _ (h2 w)
  choose y hyL hy using hl'
  have hx : Continuous fun t : Γ => s (x'' t) :=
    (continuous_of_discreteTopology (f := s)).comp hx''
  refine ⟨(d1 D.M.ρ (fun t => s (x'' t)), fun w h => D.π w (s (x'' (P.φ w h))) + y w h),
    ⟨fun t => s (x'' t), hx, rfl, fun w => ?_⟩, ?_⟩
  · convert hyL w using 1
    funext h
    simp
  · refine Prod.ext (funext fun st => ?_) (funext fun w => funext fun h => ?_)
    · obtain ⟨a, c⟩ := st
      show g.f (d1 D.M.ρ (fun t => s (x'' t)) (a, c)) = q.1 (a, c)
      rw [h1, d1_apply, d1_apply]
      simp only [map_sub, map_add (f := _), g.equiv, hs']
    · show g.fq w (D.π w (s (x'' (P.φ w h))) + y w h) = q.2 w h
      rw [map_add (f := _), g.comm, hs', hy w h]
      simp

private theorem cocycle_descends_short_exact {D' D D'' : Dat A P} (f : D'.Hom D) (g : D.Hom D'') (h : Dat.SES f g)
    {p : D.C2} (hp : p ∈ D.selmerSecondCocycles) (h0 : g.c2 p = 0) : ∃ p' ∈ D'.selmerSecondCocycles, f.c2 p' = p := by
  have e1 : ∀ st, g.f (p.1 st) = 0 := fun st => congrFun (congrArg Prod.fst h0) st
  have e2 : ∀ w t, g.fq w (p.2 w t) = 0 := fun w t =>
    congrFun (congrFun (congrArg Prod.snd h0) w) t
  choose a ha using fun st => (h.ex (p.1 st)).1 (e1 st)
  choose c hc using fun w t => (h.exq w (p.2 w t)).1 (e2 w t)
  obtain ⟨⟨hpc, hpcoc⟩, hpw⟩ := hp
  refine ⟨(a, c), ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩,
    Prod.ext (funext ha) (funext fun w => funext (hc w))⟩
  · have ea : a = fun st => Function.invFun f.f (p.1 st) := funext fun st =>
      h.inj (by rw [ha]; exact (Function.invFun_eq ⟨a st, ha st⟩).symm)
    show Continuous a
    rw [ea]
    exact (continuous_of_discreteTopology (f := Function.invFun f.f)).comp hpc
  · intro u v k
    apply h.inj
    rw [map_zero]
    simp only [map_sub, map_add (f := _), f.equiv, ha]
    exact hpcoc u v k
  · have ec : c w = fun t => Function.invFun (f.fq w) (p.2 w t) := funext fun t =>
      h.injq w (by rw [hc]; exact (Function.invFun_eq ⟨c w t, hc w t⟩).symm)
    show Continuous (c w)
    rw [ec]
    exact (continuous_of_discreteTopology (f := Function.invFun (f.fq w))).comp (hpw w).1
  · intro u v
    apply h.injq w
    rw [f.comm, ha, (hpw w).2 u v, d1_apply, d1_apply]
    simp only [map_sub, map_add (f := _), f.equivq, hc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.B2.exactMid :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D' D D'' : Dat A P) (f : D'.Hom D) (g : D.Hom D''), Dat.SES f g → (∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s) → LinearMap.ker g.h2 ≤ LinearMap.range f.h2 := by
  intro A Γ _ _ _ _ P D' D D'' f g h hl z hz
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hq : g.c2 p.1 ∈ D''.selmerSecondCoboundaries := hz
  obtain ⟨b, hb, hbq⟩ := coboundary_lift_local_conditions g h.surj hl hq
  have hm : p.1 - b ∈ D.selmerSecondCocycles := sub_mem p.2 (coboundary_mem_cocycles_local D hb)
  have h0 : g.c2 (p.1 - b) = 0 := by rw [map_sub, hbq, sub_self]
  obtain ⟨p', hp', hfp⟩ := cocycle_descends_short_exact f g h hm h0
  rw [LinearMap.mem_range]
  refine ⟨Submodule.Quotient.mk ⟨p', hp'⟩, ?_⟩
  rw [Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  show f.c2 p' - p.1 ∈ D.selmerSecondCoboundaries
  rw [hfp, sub_sub_cancel_left]
  exact neg_mem hb
end

section

namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L)

def inV (v : L.Vl) : (plOf G).ι := Sum.inl v

def inU (u : L.St) : (plOf G).ι := Sum.inr u

end UpperTheory.V.Pa.B2
end

section

noncomputable section

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
  (X : Type) [CommRing X] [Algebra x.A X]

structure IsOd (D : Dat x.A (plOf G)) where
  e : D.M.X ≃ₗ[x.A] Od x.A X n x.a
  act : ∀ (g : G.G₀) m, (e (D.M.ρ g m) : Matrix (Fin n) (Fin n) X) = x.ρX X (h.p₀ g) * e m * x.ρX X (h.p₀ g⁻¹)
  actc : ∀ m, (e (D.M.ρ G.c m) : Matrix (Fin n) (Fin n) X) = -(e m : Matrix (Fin n) (Fin n) X)ᵀ
  kerV : ∀ v m, D.π (.inl v) m = 0 ↔ ∀ i j, j < i → (x.wiX X v * (e m : Matrix (Fin n) (Fin n) X) * x.wX X v) i j = 0
  kerU : ∀ u, Function.Injective (D.π (.inr u))

variable {h x X} {X' : Type} [CommRing X'] [Algebra x.A X'] {D D' : Dat x.A (plOf G)}

def Induced (o : IsOd h x X D) (o' : IsOd h x X' D') (u : X →ₗ[x.A] X') (f : D.Hom D') : Prop :=
  ∀ m, (o'.e (f.f m) : Matrix (Fin n) (Fin n) X') = (o.e m : Matrix (Fin n) (Fin n) X).map u

def ObstructionBoundFromDuality : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x)
    (al : Fin T.q → Fin n → x.A) (d : ℕ), l ≠ 2 → (∃ dv, CohAx G0 d dv) → (∀ N, ∃ dv, CohAx (T.GN N) d dv) →
    (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → T.Eig x al → T.B2 k

end UpperTheory.V.Pa.B2
end
end
