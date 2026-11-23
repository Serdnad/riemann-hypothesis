module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle500
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle499
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle450

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.OrderUnits

variable {E : Type} [Field E] [NumberField E]

theorem ball_mem_nhds (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : P.adicCompletion E) :
    {x : P.adicCompletion E | Valued.v (x - z) ≤ WithZero.exp (-(n : ℤ))} ∈ 𝓝 z := by
  set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht
  have hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ)) := by
    have h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec P
    rw [ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]
    simp
  have hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E) := by fun_prop
  have ho := (Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc
  refine mem_of_superset (ho.mem_nhds ?_) ?_
  · show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring
    rw [sub_self, zero_div]; exact zero_mem _
  · intro x hx
    have hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1 := hx
    rw [map_div₀, hv, div_le_one₀ (WithZero.exp_pos)] at hx'
    exact hx'

theorem val_int_le (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_le_pow_iff_mem b n).2 hb

theorem exists_cong {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
  have hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P := fun P =>
    RestrictedProduct.continuous_eval P
  have hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro P _
    exact (hev P).tendsto z (ball_mem_nhds P n (z P))
  have hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E)) := hz
  obtain ⟨x, ⟨k, hk, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hk
  refine ⟨a, fun P hP => ?_⟩
  have hb' : b ∈ P.asIdeal ^ n := by
    have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n := by
      refine (Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      exact (hS P hP).ge
    exact h1 hb
  have h2 := val_int_le P n b hb'
  have h3 := hx P hP
  rw [map_add (f := _)] at h3
  have h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P =
      ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) -
        algebraMap E (Af E) (algebraMap (𝓞 E) E b) P := by
    change _ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _
    ring
  rw [h4]
  exact Valuation.map_sub_le _ h3 h2

theorem val_le_one {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_cong (P.under (OF E)) 0 (by simp) {P} (fun P' hP' => by
    rw [Finset.mem_singleton.1 hP']; rfl) hz
  have h1 := ha P (Finset.mem_singleton_self P)
  have h2 := val_int_le P 0 (algebraMap (OF E) (𝓞 E) a) (by simp)
  have h3 : z P = algebraMap E (Af E) (algebraMap (OF E) E a) P - (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) := by
    ring
  rw [h3]
  exact (Valuation.map_sub_le _ h2 h1).trans_eq (by simp)

theorem val_eq_one {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by
  have h1 := val_le_one (mem_hatOUnits.1 hy).1 P
  have h2 := val_le_one (mem_hatOUnits.1 hy).2 P
  have h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1 := by
    rw [← map_mul]
    exact (congrArg Valued.v (coord P y).val_inv).trans (map_one _)
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((y : Af E) P) * 1 := by gcongr
      _ = _ := mul_one _)

theorem finPart_eq_one_of_level {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by
  refine Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hO : ∀ P ∈ S, Over P v := fun P hP => by
    rw [hS] at hP
    unfold Formalism.L2.Host.aboveF at hP
    rw [Set.Finite.mem_toFinset] at hP
    have : P.under (OF E) = v := hP
    rw [← this]; rfl
  obtain ⟨n, hn, hlev⟩ := hl v
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)
  obtain ⟨a, ha⟩ := exists_cong v n hn S hO (mem_hatOUnits.1 hy).1
  have hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1 := fun P hP => by
    have hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P) := by
      rw [val_eq_one hy P]
      refine (ha P hP).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]
  by_cases h0 : algebraMap (OF E) E a = 0
  · refine Finset.prod_eq_one fun P hP => ?_
    have h1 := hva P hP
    rw [h0, map_zero] at h1
    exact absurd (h1.symm.trans (map_zero _)) one_ne_zero
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 (a : maximalRealSubfield E)
    (fun h1 => h0 (congrArg Subtype.val h1))
  have h2 := hF.1 v k'
  unfold Formalism.L2.Host.HChar.resFin at h2
  rw [MonoidHom.finsetProd_apply] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun P hP => ?_
  set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu
  have hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P := rfl
  have hvu : Valued.v (u : P.adicCompletion E) = 1 := hva P hP
  show χ.loc P (coord P y) = χ.loc P u
  have h3 : χ.loc P (u / coord P y) = 1 := by
    refine hlev P (hO P hP) _ ?_ ?_
    · show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']
      exact ha P hP
  rw [map_div, div_eq_one] at h3
  exact h3.symm

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
      ∀ y ∈ hatOUnits (condQ 𝔣 Q), finPart χ y = 1 := by
  intro E _ _ _ I _ φ _ s κ 𝔣 Q χ _ _ _ hχ y hy
  refine finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hy
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

end GlobalTheory.CMVal.OrderUnits
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory

theorem basisLin_oLinear : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  intro p _ D H Y AH _ _ actH u hu ιO ιL bO bL hb

  have hcomp : ∀ (f : Y ⟶ AH) (b c : D.O), f ≫ actH.act (b + c) = (f ≫ actH.act b) * (f ≫ actH.act c) := by
    intro f b c
    rw [actH.add, MonObj.comp_mul]

  have u0 : u 0 = 1 := by
    have h := hu 0 0
    simp only [add_zero] at h
    have := congrArg (fun t => t * (u 0)⁻¹) h
    simpa using this.symm
  let U : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x)
      map_zero' := by simp [u0]
      map_add' := fun x y => by simp [hu] }

  have step1 : ∀ i (c : D.O), u (c • bL i) = u (bL i) ≫ actH.act c := by
    intro i
    let F : D.O →+ Additive (Y ⟶ AH) := U.comp ((LinearMap.toSpanSingleton D.O D.La (bL i)).toAddMonoidHom)
    let G : D.O →+ Additive (Y ⟶ AH) :=
      { toFun := fun c => Additive.ofMul (u (bL i) ≫ actH.act c)
        map_zero' := by
          have h := hcomp (u (bL i)) 0 0
          simp only [add_zero] at h
          have : u (bL i) ≫ actH.act 0 = 1 := by
            have := congrArg (fun t => t * (u (bL i) ≫ actH.act 0)⁻¹) h
            simpa using this.symm
          simp [this]
        map_add' := fun b c => by simp [hcomp] }
    have hFG : F.toIntLinearMap = G.toIntLinearMap := bO.ext fun j => by
      simp [F, G, U, hb]
    intro c
    have := congrArg (fun L => L c) hFG
    simpa [F, G, U] using this
  intro c
  let F : D.La →+ Additive (Y ⟶ AH) := U.comp (DistribSMul.toAddMonoidHom D.La c)
  let G : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x ≫ actH.act c)
      map_zero' := by
        haveI := actH.hom c
        simp [u0, MonObj.one_comp]
      map_add' := fun x y => by
        haveI := actH.hom c
        simp [hu, MonObj.mul_comp] }
  have hFG : F.toIntLinearMap = G.toIntLinearMap := bL.ext fun i => by
    simp [F, G, U, step1]
  intro x
  have := congrArg (fun L => L x) hFG
  simpa [F, G, U] using this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul_left hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {S : Scheme.{0}}

def transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ h)

def lbPow {X : Scheme.{0}} (L : LB X) (m : ℕ) : LB X :=
  LB.LinComb L (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1)

def sq2 {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (ψ : A ⟶ A') :
    (G2 A).left ⟶ (G2 A').left :=
  (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem eta_zero {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

def heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_heckeSub {b : Base D R} {M : ℕ} {s : S ⟶ Sp R} (o : Obj b M s) (g : D.La →ₗ[D.O] D.La) (N : ℕ)
    (x : D.La) : o.eta (N • g x) ∈ heckeSub o g N := ⟨x, rfl⟩

theorem one_comp_transl {A : Over S} [GrpObj A] (h : 𝟙_ (Over S) ⟶ A) : (1 : 𝟙_ (Over S) ⟶ A) ≫ transl h = h := by
  rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (1 ≫ toUnit A) (𝟙 _),
    Category.id_comp, _root_.one_mul]

theorem comp_eq_one_of_transl {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A ⟶ A') [IsMonHom ψ]
    (h : 𝟙_ (Over S) ⟶ A) (hh : (transl h).left ≫ ψ.left = ψ.left) : h ≫ ψ = 1 := by
  have e : transl h ≫ ψ = ψ := Over.OverMorphism.ext hh
  rw [← one_comp_transl h, Category.assoc, e, one_comp]

end GlobalTheory.UPel.HT.Hecke
end
end

section

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open NumberField

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem sq_two_mul_rho_sub_tr (b : Base D R) :
    (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
  have h := b.ρ_root
  push_cast
  linear_combination 4 * h

theorem isUnit_two_mul_rho_sub_tr (b : Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hp : (p).Prime := Fact.out
  set d : ℤ := D.tr ^ 2 - 4 * D.nm with hd
  have hc : d.natAbs.Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => D.disc_p ?_)
    exact Int.natCast_dvd.2 h
  have hu := b.unit _ hc
  have hdu : IsUnit ((d : ℤ) : R) := by
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast]; exact hu
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  rw [← sq_two_mul_rho_sub_tr] at hdu
  exact (isUnit_pow_iff two_ne_zero).1 hdu

def uInv (b : Base D R) : R := ↑(isUnit_two_mul_rho_sub_tr b).unit⁻¹

theorem uInv_mul (b : Base D R) : uInv b * (2 * b.ρ - (D.tr : R)) = 1 :=
  (isUnit_two_mul_rho_sub_tr b).val_inv_mul

def comaxC (b : Base D R) (i j : Fin D.a) : 𝓞 D.F →₀ R :=
  if h : i ≠ j then
    Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))
  else 0

theorem comaxC_spec (b : Base D R) {i j : Fin D.a} (h : i ≠ j) :
    ((comaxC b i j).sum fun x r => r * (b.t i x - b.t j x)) = 1 := by
  unfold comaxC
  rw [dite_eq_left h]
  exact Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))

variable {B : Type} [CommRing B] {n : ℕ}

def alphaMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i j : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (comaxC b i j).sum fun x r =>
    algebraMap B (Matrix (Fin n) (Fin n) B) (βB r) * (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x)))

def projMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun j => if j = i then 1 else alphaMat b βB M i j).prod *
    (algebraMap B (Matrix (Fin n) (Fin n) B) (βB (uInv b)) *
      (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))))

end GlobalTheory.UPel.HT.LieLin.RankIdeal
end
end

section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc

theorem _root_.GlobalTheory.T.spec_functions_eq_of_restrictions_on_pairs : ∀ {X : Scheme.{0}} (B B' : Type) [CommRing B] [CommRing B'] (x : Sp B ⟶ X) (ψ : Sp B' ⟶ Sp B) (a b : B'), (∀ (V' : (Sp B').affineOpens) (p : Pair x), V'.1 ≤ ψ ⁻¹ᵁ p.1.1.1 → (secMap (𝟙 (Sp B')) V'.1).hom a = (secMap (𝟙 (Sp B')) V'.1).hom b) → a = b := by
  first | exact @GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | exact GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs | (intros; apply GlobalTheory.CechDR.AffLoc.eq_of_secMap_eq_on_pairs <;> assumption)
end
