module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle052
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle084
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem unitAt_natCast_of_overZp (𝔐 : HodgeCpt Y S y) (p : ℕ) (q : Cpt 𝔐.ξ) (hq : OverZp 𝔐 p q) (b : ℕ)
    (hb : ¬ p ∣ b) : unitAt 𝔐.ξ q (b : Ω) := by
  induction b using Nat.recOnMul with
  | zero => exact absurd (dvd_zero p) hb
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, one_mem _, by rw [inv_one]; exact one_mem _⟩
  | prime r hr =>
    by_contra h
    exact hb (by rw [hq r hr h])
  | mul a b iha ihb =>
    have ha := iha fun h => hb (h.mul_right b)
    have hb' := ihb fun h => hb (h.mul_left a)
    rw [Nat.cast_mul]
    exact ⟨mul_ne_zero ha.1 hb'.1, mul_mem ha.2.1 hb'.2.1, by
      rw [mul_inv]; exact mul_mem ha.2.2 hb'.2.2⟩

theorem isLocIn_regAt_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (s : ∀ k, J k) (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) s q → OverZp 𝔐 p q → HTL.IsLocIn (chartRing o (mseg y) s) (regAt 𝔐.ξ q) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ o _ _ ho s q hs hq
  have hu := unitAt_natCast_of_overZp 𝔐 p q hq
  refine ⟨fun a => ?_, fun b hb => ?_⟩
  · obtain ⟨a, ha⟩ := a
    show a ∈ regAt 𝔐.ξ q
    refine Algebra.adjoin_induction (p := fun x _ => x ∈ regAt 𝔐.ξ q) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩
      exact hs.2 j
    · intro r
      obtain ⟨m, n, hn, e⟩ := (ho _).1 ⟨r, rfl⟩
      rw [e, div_eq_mul_inv]
      exact mul_mem (intCast_mem _ m) (hu n hn).2.2
    · intro x z _ _ hx hz
      exact add_mem hx hz
    · intro x z _ _ hx hz
      exact mul_mem hx hz
  · obtain ⟨t, ht, hut, htb⟩ := (GlobalTheory.T.regAt_iff_chart_localization 𝔐.X Ω 𝔐.ξ ℤ _ (mseg y) 𝔐.tie s q hs b).1 hb
    have hle : ∀ x ∈ Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y s),
        x ∈ chartRing o (mseg y) s := by
      intro x hx
      refine Algebra.adjoin_induction (p := fun x _ => x ∈ chartRing o (mseg y) s) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        exact div_mem_chartRing _ _ _
      · intro n
        simp
      · intro x z _ _ hx hz
        exact add_mem hx hz
      · intro x z _ _ hx hz
        exact mul_mem hx hz
    exact ⟨⟨t, hle t ht⟩, ⟨t * b, hle _ htb⟩, hut.1, hut.2.2, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem pow_smul_mem_om_of_overlap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (Dc : ∀ s : {s : ∀ k, J k // mseg y s ≠ 0}, HTChart (chartRing o (mseg y) s.1) Ω (cmConj E) p (𝔐.R p) (D.p + D.q) (Module.Dual Ω 𝔐.Li)), IsHTFamily 𝔐 p o Dc → ∀ (s t : {s : ∀ k, J k // mseg y s ≠ 0}) (w : Module.Dual Ω 𝔐.Li), (∀ q, InChart 𝔐.ξ (mseg y) s.1 q → InChart 𝔐.ξ (mseg y) t.1 q → OverZp 𝔐 p q → w ∈ 𝔐.M.omLat q) → ∃ n : ℕ, (mseg y s.1 / mseg y t.1) ^ n • w ∈ (Dc t).om := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p _ hpS o _ _ ho Dc hfam s t w hw
  have hp : p.Prime := Fact.out
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hs0 : mseg y s.1 ≠ 0 := s.2
  have ht0 : mseg y t.1 ≠ 0 := t.2
  have hfA : (mseg y s.1 / mseg y t.1) ∈ chartRing ℤ (mseg y) t.1 := div_mem_chartRing (mseg y) t.1 s.1
  have hle : ∀ a ∈ chartRing ℤ (mseg y) t.1, a ∈ chartRing o (mseg y) t.1 := by
    intro a ha
    have h2 : chartRing ℤ (mseg y) t.1 ≤ (chartRing o (mseg y) t.1).restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := o))
    exact h2 ha
  have hsm : ∀ a ∈ chartRing o (mseg y) t.1, ∀ e ∈ (Dc t).om, a • e ∈ (Dc t).om := by
    intro a ha e he
    have := (Dc t).om.smul_mem (⟨a, ha⟩ : chartRing o (mseg y) t.1) he
    rwa [Subalgebra.smul_def] at this
  have hinv : ∀ b : ℕ, ¬ p ∣ b → ((b : Ω))⁻¹ ∈ chartRing o (mseg y) t.1 := by
    intro b hb
    obtain ⟨r, hr⟩ := (ho ((b : Ω))⁻¹).2 ⟨1, b, hb, by simp⟩
    rw [← hr]
    exact Subalgebra.algebraMap_mem _ r
  by_contra hcon
  push_neg at hcon
  let I : Ideal (chartRing ℤ (mseg y) t.1) :=
    { carrier := {a | (a : Ω) • w ∈ (Dc t).om}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ (mseg y) t.1) : Ω) • w ∈ (Dc t).om
        rw [smul_eq_mul, Subalgebra.coe_mul, mul_smul]
        exact hsm _ (hle _ a.2) _ hu }
  let T : Submonoid (chartRing ℤ (mseg y) t.1) :=
    { carrier := {u | ∃ b n : ℕ, ¬ p ∣ b ∧ (b : Ω) ≠ 0 ∧ (u : Ω) = (b : Ω) * (mseg y s.1 / mseg y t.1) ^ n}
      one_mem' := ⟨1, 0, hp.not_dvd_one, by simp, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, n, hb, hb0, hu⟩ ⟨b', n', hb', hb0', hv⟩
        refine ⟨b * b', n + n', fun h => (hp.dvd_mul.1 h).elim hb hb', by push_cast; exact mul_ne_zero hb0 hb0', ?_⟩
        rw [Subalgebra.coe_mul, hu, hv]
        push_cast
        ring }
  have hdisj : Disjoint (I : Set (chartRing ℤ (mseg y) t.1)) (T : Set (chartRing ℤ (mseg y) t.1)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, n, hb, hb0, hub⟩
    have hu' : ((b : Ω) * (mseg y s.1 / mseg y t.1) ^ n) • w ∈ (Dc t).om := by rw [← hub]; exact hu
    have h2 := hsm _ (hinv b hb) _ hu'
    rw [smul_smul, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul] at h2
    exact hcon n h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨q, hq, hqP⟩ := TieVB.exists_point hT ht0 P hP
  have notP : ∀ u ∈ T, u ∉ P := fun u hu huP => Set.disjoint_left.1 hPT huP hu
  have hfu : unitAt 𝔐.ξ q (mseg y s.1 / mseg y t.1) := by
    by_contra hn
    exact notP ⟨(mseg y s.1 / mseg y t.1), hfA⟩ ⟨1, 1, hp.not_dvd_one, by simp, by simp⟩ ((hqP ⟨(mseg y s.1 / mseg y t.1), hfA⟩).2 hn)
  have hOver : OverZp 𝔐 p q := by
    intro r hr hfib
    by_contra hrp
    have hrp' : ¬ p ∣ r := fun h => hrp ((Nat.prime_dvd_prime_iff_eq hp hr).1 h).symm
    by_cases hr0 : (r : Ω) = 0
    · apply hcon 0
      rw [pow_zero, one_smul, hfam.om_iff t w]
      intro q' _ hq'
      exact absurd (hq' r hr (fun hu => hu.1 hr0)) hrp
    have hrT : (r : chartRing ℤ (mseg y) t.1) ∈ T :=
      ⟨r, 0, hrp', hr0, by simp⟩
    have hu := not_not.1 (mt (hqP (r : chartRing ℤ (mseg y) t.1)).2 (notP _ hrT))
    apply hfib
    simpa using hu
  have hqs : InChart 𝔐.ξ (mseg y) s.1 q := by
    refine ⟨hs0, fun c' => ?_⟩
    have he : mseg y c' / mseg y s.1 = mseg y c' / mseg y t.1 * (mseg y s.1 / mseg y t.1)⁻¹ := by
      rw [inv_div]
      field_simp
    rw [he]
    exact mul_mem (hq.2 c') hfu.2.2
  have hwq := hw q hqs hq hOver
  rw [hfam.om_loc t q hq hOver] at hwq
  obtain ⟨s₀, hs₀A, hs₀u, hs₀M⟩ := TieVB.exists_den_span hT hq ((Dc t).om.toAddSubgroup)
    (fun a ha e he => hsm a (hle a ha) e he)
    (show w ∈ Submodule.span _ (((Dc t).om.toAddSubgroup : Set (Module.Dual Ω 𝔐.Li))) from hwq)
  have hI : (⟨s₀, hs₀A⟩ : chartRing ℤ (mseg y) t.1) ∈ I := hs₀M
  exact (hqP ⟨s₀, hs₀A⟩).1 (hIP hI) hs₀u

end GlobalTheory.CompanionTheory.Ar.HT
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_hChart_of_extendsUnitAt : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  intro X s Ω _ ξ W U N F T t v d B Y b₁ hξ hY hb₁ hN hNU hW hv hg hT hE
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap]
  obtain ⟨ε, h', hε, hd, h0, hrel⟩ := hE d B Y hY.isOpen hY.hol
    (fun b hb => (hY.isOver b hb).trans hid.symm) b₁ hb₁ rfl
  have hopen : IsOpen (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) :=
    hd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hB₂ : IsOpen (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) := hY.isOpen.inter hopen
  have hsub : B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) ⊆ B := Set.inter_subset_left
  have htop : ∀ b ∈ B, ⊤ ≤ Y b ⁻¹ᵁ N := fun b hb => (top_le_iff_centre _ _).2 (hN b hb).1
  refine ⟨B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ), fun b => h' b * valAt' (Y b) N v,
    ⟨hb₁, Metric.mem_ball_self hε, h0⟩, ?_⟩
  refine
    { chart := by
        refine { isOpen := hB₂, hol := ?_, isOver := fun b hb => hY.isOver b (hsub hb), factor := ?_ }
        · intro U f
          have e : {b ∈ B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) | ⊤ ≤ Y b ⁻¹ᵁ U} =
              (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
            ext b
            exact ⟨fun hb => ⟨hb.1, hsub hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
          rw [e]
          exact ⟨hB₂.inter (hY.hol U f).1, (hY.hol U f).2.mono Set.inter_subset_right⟩
        · intro m B' y oB hy ov b₀ h₀ b₂ h₂ e
          obtain ⟨ε', κ, ε0, sub, dκ, k₀, hκ⟩ := hY.factor m B' y oB hy ov b₀ h₀ b₂ (hsub h₂) e
          have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
          have m₂ : κ ⁻¹' (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) ∈ 𝓝 b₀ :=
            c.preimage_mem_nhds (hB₂.mem_nhds (k₀ ▸ h₂))
          obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
          have sb : ball b₀ δ ⊆ ball b₀ ε' := fun b hb => (hδ hb).2
          exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩
      inU := fun b hb => hNU (hN b hb.1).1
      cpt := fun b hb => (hN b hb.1).2
      dense := fun O oO sO nO => hW O oO (sO.trans hsub) nO
      hol := ?_
      ne := ?_
      rel := ?_ }
  · refine DifferentiableOn.mul (hd.mono fun b hb => hb.2.1) ?_
    exact (hY.hol N v).2.mono fun b hb => ⟨hb.1, htop b hb.1⟩
  · intro b hb
    refine mul_ne_zero hb.2.2 ?_
    intro hz
    obtain ⟨u, rfl⟩ := hv
    have e := valAt'_mul (Y b) N u.val u⁻¹.val
    rw [Units.mul_inv, valAt'_one (Y b) N (htop b hb.1), hz, zero_mul] at e
    exact one_ne_zero e
  · intro b hb hWb r hr
    have e₁ : ValAt ξ (Y b) (t / T) (valAt' (Y b) N v) :=
      ValAt.of_section (hN b hb.1).1 (hN b hb.1).2 (hg _ _ _)
    have e₂ : ValAt ξ (Y b) t (valAt' (Y b) N v * r) := by
      have := ValAt.mul e₁ hr
      rwa [div_mul_cancel₀ _ hT] at this
    rw [hrel b ⟨hb.1, hb.2.1⟩ ((top_le_iff_centre _ _).2 hWb) _ e₂, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LieTransport

private theorem mul_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact h.2 T x y x₀ y₀ hx hy

private theorem one_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ)
    (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have hm : (o * o).left = o.left := by
    rw [mul_left_eq_of_isGrpPullback h T _ rfl 1 1 o o rfl rfl, _root_.mul_one]
    rfl
  have ho : o * o = o := Over.OverMorphism.ext hm
  have ho1 : o = 1 := by
    have := congrArg (· * o⁻¹) ho
    simpa [_root_.mul_assoc] using this
  rw [← ho1]
  rfl

private theorem specMap_fstHom_comp_algebraMap_eq_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

private theorem exists_lieModel_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S') (x' : Spec (CommRingCat.of R) ⟶ S) (hx : x' = x ≫ f)
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) :
    ∃ N : LieModel G x' W, ∀ e, (N.pt e).left = (M.pt e).left ≫ φ := by
  subst hx
  have hw : ∀ e, ((M.pt e).left ≫ φ) ≫ G.hom = (epsAt (x ≫ f)).hom := by
    intro e
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    simp [epsAt]
  let P : W → (epsAt (x ≫ f) ⟶ G) := fun e =>
    Over.homMk (U := epsAt (x ≫ f)) (V := G) ((M.pt e).left ≫ φ) (hw e)
  have hP : ∀ e, (P e).left = (M.pt e).left ≫ φ := fun e => rfl
  have one_eq := one_left_eq_of_isGrpPullback h (Over.mk x) (x ≫ f) rfl
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x ≫ f =
      (epsAt x).hom ≫ f := by simp [epsAt]
  refine ⟨⟨P, ?_, ?_, ?_, ?_, ?_⟩, hP⟩
  · intro e
    have ht := M.tan e
    unfold IsTanAt at ht ⊢
    rw [hP, ← Category.assoc, ht]
    exact one_eq.symm
  · intro e e' hee
    apply M.inj
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · have := congrArg Over.Hom.left hee
      simpa [P] using this
    · rw [Over.w, Over.w]
  · intro v hv
    have hvw : v.left ≫ G.hom = (epsAt x).hom ≫ f := by
      rw [Over.w]; simp [epsAt]
    let v' : epsAt x ⟶ G' := Over.homMk (h.1.lift v.left (epsAt x).hom hvw) (h.1.lift_snd _ _ _)
    have hv' : IsTanAt G' x v' := by
      unfold IsTanAt at hv ⊢
      apply h.1.hom_ext
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_fst]
        rw [hv, one_eq]
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_snd]
        rw [Over.w]
        simp only [epsAt, Over.mk_hom]
        rw [← Category.assoc, specMap_fstHom_comp_algebraMap_eq_id, Category.id_comp]
    obtain ⟨e, he⟩ := M.onto v' hv'
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ φ = v.left
    rw [he]
    exact h.1.lift_fst _ _ _
  · intro e e'
    apply Over.OverMorphism.ext
    have hm := mul_left_eq_of_isGrpPullback h (epsAt x) _ hg (M.pt e) (M.pt e') (P e) (P e') (hP e) (hP e')
    refine Eq.trans ?_ hm.symm
    rw [hP, M.add]
  · intro c e
    show (M.pt (c • e)).left ≫ φ = _
    rw [M.smul, Category.assoc]
    rfl

private theorem exists_isActOf_geometry {S : Scheme} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {W : Type} [AddCommGroup W] [Module R W]
    (M : LieModel G x W) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ ρ : O →+* Module.End R W, M.IsActOf a.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h0 := M.add 0 0
    rw [add_zero] at h0
    have := congrArg (· * (M.pt 0)⁻¹) h0
    simpa [_root_.mul_assoc] using this.symm
  have tan : ∀ (b : O) (e : W), IsTanAt G x (M.pt e ≫ a.act b) := by
    intro b e
    have ht := M.tan e
    have hh := a.hom b
    unfold IsTanAt at ht ⊢
    rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]
  choose A hA using fun (b : O) (e : W) => M.onto (M.pt e ≫ a.act b) (tan b e)
  have hadd : ∀ b e e', A b (e + e') = A b e + A b e' := by
    intro b e e'
    have hh := a.hom b
    apply M.inj
    rw [hA, M.add, M.add, hA, hA, MonObj.mul_comp]
  have hsmul : ∀ b (c : R) e, A b (c • e) = c • A b e := by
    intro b c e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hA, Over.comp_left, M.smul, M.smul, hA, Over.comp_left, Category.assoc]
  let L : O → Module.End R W := fun b =>
    { toFun := A b, map_add' := hadd b, map_smul' := fun c e => by simpa using hsmul b c e }
  have hL : ∀ b e, L b e = A b e := fun _ _ => rfl
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, hA, a.one, Category.comp_id]
    rfl
  have hmul : ∀ b b', L (b * b') = L b * L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, hA, hA, hA, mul_comm, a.mul, Category.assoc]
  have haddL : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [LinearMap.add_apply, hL, hL, hL, hA, M.add, hA, hA, a.add, MonObj.comp_mul]
  let ρ : O →+* Module.End R W := RingHom.mk' ⟨⟨L, hone⟩, hmul⟩ haddL
  exact ⟨ρ, fun b e => hA b e⟩

private theorem isActOf_of_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S'} {x' : Spec (CommRingCat.of R) ⟶ S}
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) (N : LieModel G x' W)
    (hN : ∀ e, (N.pt e).left = (M.pt e).left ≫ φ) {O : Type} [CommRing O]
    (act' : O → (G' ⟶ G')) (act : O → (G ⟶ G))
    (hact : ∀ b, (act' b).left ≫ φ = φ ≫ (act b).left)
    (ρ : O →+* Module.End R W) (hM : M.IsActOf act' ρ) : N.IsActOf act ρ := by
  intro b e
  apply Over.OverMorphism.ext
  have h1 := hM b e
  rw [hN, h1, Over.comp_left, Over.comp_left, hN, Category.assoc, hact, Category.assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  intro E _ _ _ H D l Xo c O _ β Y F _ y
  obtain ⟨W, i1, i2, ⟨M0⟩⟩ := lieModel_exists _ Y.oF.t.G F y
  obtain ⟨ρ, hρ⟩ := exists_isActOf_geometry M0 Y.oF.t.act
  obtain ⟨Mu, hMu⟩ := exists_lieModel_pullback Y.m0.toSABMap.cart y (under y) rfl M0
  obtain ⟨Mz, hMz⟩ := exists_lieModel_pullback Y.m.cart y (y ≫ Y.j) rfl M0
  refine ⟨W, i1, i2, Mu, Mz, ρ, ?_, ?_, ?_⟩
  · exact isActOf_of_pullback M0 Mu hMu _ _ (fun b => Y.m0.toSABMap.act b) ρ hρ
  · exact isActOf_of_pullback M0 Mz hMz _ _ (fun b => Y.m.act b) ρ hρ
  · intro e
    unfold SameVec
    exact ⟨(M0.pt e).left, Over.w (M0.pt e), (hMu e).symm, (hMz e).symm⟩

end GlobalTheory.CompanionTheory.Ar.LieTransport
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

def IsPullWedge {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]
    (i : Ω₀ →+* Ω) (j : V₀ →+ V) {n : ℕ} (a : ⋀[Ω₀]^n V₀) (a' : ⋀[Ω]^n V) : Prop :=
  ∀ (b : Fin n → V₀) (α : Ω₀), a = α • exteriorPower.ιMulti Ω₀ n b →
    a' = i α • exteriorPower.ιMulti Ω n fun k => j (b k)

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

def IsTie (Z : CptOver Y U) (𝔐 : HodgeCpt Y S y) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) : Prop :=
  Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f i ∧ i.comp Z.inc = 𝔐.cst ∧ IsExtOver i j ∧
    ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (Z.M.pt e).left

end Comparison₂

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end
