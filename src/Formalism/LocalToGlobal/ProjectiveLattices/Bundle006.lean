module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalProperties.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle005

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Pj

section Charts

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev locM (K : Type) [Field K] {S : Type} [CommRing S] [Algebra K S] (m : Ideal S) [m.IsPrime] :
    S →ₐ[K] Localization.AtPrime m :=
  IsScalarTower.toAlgHom K S (Localization.AtPrime m)

def FrChartAt {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] (A : TRing K)
    (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (a : A.R →ₐ[K] p'.R) (μ : p'.R →ₐ[K] Localization.AtPrime m)
      (y' : pts p'.R), mapR lam y y' ∧ mapR a u y' ∧ μ.comp lam = (locM K m).comp φ ∧ μ.comp a = c

def FrChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m), FrChartAt pts mapR w m A u c

def BorChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
    ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m) (B : TRing K) (uB uB' : pts B.R)
        (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R) (cB : B.R →ₐ[K] Localization.AtPrime m),
        FrChartAt pts mapR w m A u c ∧ FrChartAt pts mapR w' m A u c' ∧ mapR π u uB ∧ mapR π' u uB' ∧
          borR tB uB uB' ∧ cB.comp π = c ∧ cB.comp π' = c' ∧ ∀ i, cB (tB i : B.R) = locM K m (t i : S)

variable {pts mapR borR}

theorem chartAt_val {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by
  obtain ⟨p', lam, a, μ, y', h1, h2, h3, h4⟩ := hc p φ y hy
  have e1 : f p' y' = lam (f p y) := hf p p' lam y y' h1
  have e2 : f p' y' = a (f A u) := hf A p' a u y' h2
  calc locM K m (φ (f p y)) = ((locM K m).comp φ) (f p y) := rfl
    _ = (μ.comp lam) (f p y) := by rw [h3]
    _ = μ (f p' y') := by rw [e1]; rfl
    _ = (μ.comp a) (f A u) := by rw [e2]; rfl
    _ = c (f A u) := by rw [h4]

theorem eq_of_locM {S : Type} [CommRing S] [Algebra K S] {x y : S}
    (h : ∀ (m : Ideal S) (_ : m.IsMaximal), locM K m x = locM K m y) : x = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro J hJ
  haveI := hJ
  have hxy := h J hJ
  simp only [locM, IsScalarTower.coe_toAlgHom'] at hxy
  rw [map_sub, hxy, sub_self]

theorem evalWD_of_frChart (h : FrChart pts mapR) : EvalWD pts mapR := by
  intro f hf S _ _ p q φ ψ y z w hy hz
  apply eq_of_locM (K := K)
  intro m hm
  haveI := hm
  obtain ⟨A, u, c, hc⟩ := h S w m
  rw [chartAt_val hf hc hy, chartAt_val hf hc hz]

private theorem evalAt_spec_lemma {f : Rules pts} {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y0 : pts p.R),
      mapR φ y0 y ∧ evalAt pts mapR f y = φ (f p y0) := by
  refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
    hy.choose_spec.choose_spec.choose_spec, ?_⟩
  rw [evalAt, dite_eq_left hy]

theorem wtAll_of_borChart [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by
  obtain ⟨p, φ, y0, hm, hv⟩ := evalAt_spec_lemma (f := f) hy
  obtain ⟨p', φ', y0', hm', hv'⟩ := evalAt_spec_lemma (f := f) hy'
  rw [hv, hv']
  apply eq_of_locM (K := K)
  intro m hmax
  haveI := hmax
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hm', chartAt_val hf hc hm]
  calc c' (f A u) = (cB.comp π') (f A u) := by rw [e2]
    _ = cB (f B uB') := by rw [AlgHom.comp_apply, hf A B π' u uB' hπ']
    _ = cB (wchar e tB) * cB (f B uB) := by rw [hw B tB uB uB' hbB, map_mul]
    _ = locM K m (wchar e t) * c (f A u) := by
      have k1 : cB (f B uB) = c (f A u) := by rw [← e1, AlgHom.comp_apply, hf A B π u uB hπ]
      rw [k1]
      simp [wchar, map_prod, map_pow, e3, Units.coe_prod]

end Charts

end Formalism.L2.Pj
end
end

section

namespace Formalism.L2.Pj.RegB

open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal

theorem mem_loc_of_heightOne {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (qq : Ideal R) [hq : qq.IsPrime]
    (x : K) (hx : ∀ p : Ideal R, p.IsPrime → p.height = 1 → p ≤ qq →
      ∃ a s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K a) :
    ∃ a s : R, s ∉ qq ∧ x * algebraMap R K s = algebraMap R K a := by
  classical
  obtain ⟨⟨a, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors R) x
  simp only at hxs
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  have hsK : algebraMap R K (s : R) ≠ 0 := by
    intro h; apply hs0; exact hinj (by rw [h, map_zero])
  by_cases hex : ∃ t : R, t ∉ qq ∧ t * a ∈ Ideal.span {(s : R)}
  · obtain ⟨t, ht, hta⟩ := hex
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hta
    refine ⟨r, t, ht, ?_⟩
    apply mul_right_cancel₀ hsK
    rw [mul_assoc, mul_comm (algebraMap R K t), ← mul_assoc, hxs, ← map_mul, ← map_mul, mul_comm a t, ← hr,
      mul_comm]
  push Not at hex
  have hab0 : colonI (s : R) a ≤ qq := by
    intro t ht
    by_contra htq
    exact hex t htq ht
  let S : Set (Ideal R) := {J | ∃ c, J = colonI (s : R) c ∧ J ≤ qq ∧ colonI (s : R) a ≤ J}
  have hS : S.Nonempty := ⟨colonI (s : R) a, a, rfl, hab0, le_rfl⟩
  obtain ⟨J, ⟨b, rfl, hJq, hab⟩, hmax⟩ := (wellFounded_gt (α := Ideal R)).has_min S hS

  have hsat : ∀ r : R, r ∉ qq → colonI (s : R) (r * b) = colonI (s : R) b := by
    intro r hr
    have hle : colonI (s : R) b ≤ colonI (s : R) (r * b) := by
      intro y hy
      rw [mem_colonI] at *
      rw [mul_left_comm]
      exact Ideal.mul_mem_left _ _ hy
    have hq' : colonI (s : R) (r * b) ≤ qq := by
      intro y hy
      rw [mem_colonI, ← mul_assoc] at hy
      have : y * r ∈ qq := hJq hy
      rcases hq.mem_or_mem this with h | h
      · exact h
      · exact absurd h hr
    by_contra hne
    exact hmax _ ⟨r * b, rfl, hq', hab.trans hle⟩ (lt_of_le_of_ne hle (Ne.symm hne))
  set P := colonI (s : R) b with hPdef
  have hPne : P ≠ ⊤ := fun h => hq.ne_top (top_le_iff.1 (h ▸ hJq))
  have hb : b ∉ Ideal.span {(s : R)} := by
    intro hb
    apply hPne
    rw [eq_top_iff]
    intro y _
    rw [mem_colonI]
    exact Ideal.mul_mem_left _ _ hb
  have hprime : ∀ q1 q2 : R, q1 * q2 ∈ P → q1 ∈ P ∨ q2 ∈ P := by
    intro q1 q2 hq12
    by_cases h1 : q1 ∈ P
    · exact Or.inl h1
    · right
      have hle : P ≤ colonI (s : R) (q1 * b) := by
        intro y hy
        rw [mem_colonI] at *
        rw [mul_left_comm]
        exact Ideal.mul_mem_left _ _ hy
      have hq' : colonI (s : R) (q1 * b) ≤ qq := by
        intro y hy
        by_contra hyq
        apply h1
        rw [← hsat y hyq, mem_colonI]
        rw [mem_colonI] at hy
        have : q1 * (y * b) = y * (q1 * b) := by ring
        rw [this]
        exact hy
      have heq : P = colonI (s : R) (q1 * b) := by
        by_contra hne
        exact hmax _ ⟨q1 * b, rfl, hq', hab.trans hle⟩ (lt_of_le_of_ne hle hne)
      rw [heq, mem_colonI]
      rw [mem_colonI] at hq12
      have : q2 * (q1 * b) = q1 * q2 * b := by ring
      rw [this]
      exact hq12
  have hPp : P.IsPrime := ⟨hPne, fun {q1 q2} h => hprime q1 q2 h⟩
  have hsP : (s : R) ∈ P := by
    rw [mem_colonI]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hPbot : P ≠ ⊥ := by
    intro h
    apply hs0
    rw [h] at hsP
    exact (Submodule.mem_bot R).mp hsP

  have hle1 : P.height ≤ 1 := by
    by_cases hA : ∀ q ∈ P, ∀ t : R, q * b = t * s → t ∈ P
    · exfalso
      let y : K := algebraMap R K b / algebraMap R K s
      let N : Submodule R K := Submodule.map (Algebra.linearMap R K) P
      have hN : N ≠ ⊥ := by
        intro h
        have : algebraMap R K (s : R) ∈ N := ⟨s, hsP, rfl⟩
        rw [h] at this
        exact hsK ((Submodule.mem_bot R).mp this)
      have hNfg : N.FG := (IsNoetherian.noetherian P).map _
      have hint : IsIntegral R y := by
        refine isIntegral_of_smul_mem_submodule N hN hNfg y ?_
        rintro n ⟨q, hq, rfl⟩
        obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ((mem_colonI).mp hq)
        refine ⟨t, hA q hq t ht.symm, ?_⟩
        simp only [Algebra.linearMap_apply, smul_eq_mul, y]
        field_simp
        rw [← map_mul, ← map_mul, ht, mul_comm]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      apply hb
      rw [Ideal.mem_span_singleton']
      refine ⟨r, hinj ?_⟩
      rw [map_mul, hr]
      simp only [y]
      field_simp
    · push Not at hA
      obtain ⟨u, hu, t, hut, htP⟩ := hA
      have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
      apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {u}) P
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).mpr hu⟩, ?_⟩
      rintro Q ⟨hQ, huQ⟩ hQP q hq
      obtain ⟨tq, htq⟩ := Ideal.mem_span_singleton'.mp ((mem_colonI).mp hq)
      have key : q * t = u * tq := by
        apply mul_right_cancel₀ hs0
        calc q * t * s = q * (u * b) := by rw [hut]; ring
          _ = u * (q * b) := by ring
          _ = u * tq * s := by rw [← htq]; ring
      have hu' : u ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp huQ
      have : q * t ∈ Q := by rw [key]; exact Ideal.mul_mem_right _ _ hu'
      rcases hQ.mem_or_mem this with h | h
      · exact h
      · exact absurd (hQP h) htP
  have hne0 : P.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hPbot
  have h1 : P.height = 1 := le_antisymm hle1 (Order.one_le_iff_ne_zero.mpr hne0)
  obtain ⟨a', s', hs'P, hxs'⟩ := hx P hPp h1 hJq
  exfalso
  apply hs'P
  apply hab
  rw [mem_colonI, Ideal.mem_span_singleton']
  refine ⟨a', hinj ?_⟩
  rw [map_mul, map_mul, ← hxs', ← hxs]
  ring

end Formalism.L2.Pj.RegB
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {R : Type} [CommRing R] {d n : ℕ}

def Lin (b : Fin n) (v : Fin d → R) (f : PS R n d) : PS R n d :=
  ∑ j : Fin d, C (v j) * pderiv (b, j) f

def LinMon {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    PS R n d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (Lin (cp l) (u l))^[m l] g) f

def OrdGe (N : ℕ) (f : PS R n d) : Prop :=
  ∀ m : Fin n × Fin d →₀ ℕ, m.degree < N → coeff m f = 0

end Formalism.L2.Pj.Crude
end
end
