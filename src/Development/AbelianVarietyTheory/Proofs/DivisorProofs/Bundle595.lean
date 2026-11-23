module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantPDivGroupOmegaTrivialHodgeTateBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle548
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Mathlib.RingTheory.Flat.TorsionFree
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.WeilFormula

theorem setIntegral_addSubgroup_add_right {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (g : V → ℂ)
    {t : V} (ht : t ∈ L) :
    ∫ z in (L : Set V), g (z + t) ∂μ = ∫ z in (L : Set V), g z ∂μ := by
  simp_rw [add_comm _ t]
  rw [← integral_indicator hLo.measurableSet, ← integral_indicator hLo.measurableSet,
    ← integral_add_left_eq_self (μ := μ) ((L : Set V).indicator g) t]
  congr 1
  funext z
  by_cases hz : z ∈ L
  · rw [Set.indicator_of_mem (show z ∈ (L : Set V) from hz),
      Set.indicator_of_mem (show t + z ∈ (L : Set V) from L.add_mem ht hz)]
  · have hz' : t + z ∉ L := fun h => hz ((L.add_mem_cancel_left ht).1 h)
    rw [Set.indicator_of_notMem (show z ∉ (L : Set V) from hz),
      Set.indicator_of_notMem (show t + z ∉ (L : Set V) from hz')]

theorem weil_formula : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e →
    ∀ (f g : X → ℂ) (s : X → X) (γ : ℂ), Continuous f → Continuous s →
    (∀ y u, f y * e y u = g u * f (y + s u)) → HasGauss μ f γ → ∀ φ ∈ SB X, ∀ x,
    four μ e (fun y => f y * four μ e φ y) x = γ * ∫ z, g (x + z) * φ z ∂μ := by
  intro X _ _ _ _ hG μ _ e he f g s γ hf hs hfg hga φ hφ x
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hφ4 : four μ e φ ∈ SB X := GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat X hG μ e he φ hφ
  have hK1 : IsCompact (tsupport (four μ e φ)) := hφ4.2
  have hφc : IsCompact (tsupport φ) := hφ.2
  have hK2 : IsCompact (s '' ((fun z => x + z) '' tsupport φ)) :=
    (hφc.image (continuous_const.add continuous_id)).image hs
  obtain ⟨L, hLc, hLo, hKL, hLγ⟩ := hga _ (hK1.union hK2)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have he_cont : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hφcont : Continuous φ := hφ.1.continuous
  have h0 : ∀ y, y ∉ (L : Set X) → e x y * (f y * four μ e φ y) = 0 := by
    intro y hy
    have : four μ e φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hKL (Or.inl h)))
    simp [this]
  have h1 : four μ e (fun y => f y * four μ e φ y) x
      = ∫ y in (L : Set X), ∫ z, e x y * f y * (e y z * φ z) ∂μ ∂μ := by
    calc four μ e (fun y => f y * four μ e φ y) x = ∫ y, e x y * (f y * four μ e φ y) ∂μ := rfl
      _ = ∫ y in (L : Set X), e x y * (f y * four μ e φ y) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = _ := by
          congr 1; funext y
          simp only [four]
          rw [← mul_assoc, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
      ((μ.restrict (L : Set X)).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hc : Continuous (Function.uncurry fun y z => e x y * f y * (e y z * φ z)) := by
      have h1' : Continuous fun p : X × X => e x p.1 := he_cont.comp (continuous_const.prodMk continuous_fst)
      exact (h1'.mul (hf.comp continuous_fst)).mul (he_cont.mul (hφcont.comp continuous_snd))
    have hon : IntegrableOn (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
        ((L : Set X) ×ˢ tsupport φ) (μ.prod μ) := hc.continuousOn.integrableOn_compact (hLc.prod hφc)
    refine hon.of_forall_sdiff_eq_zero (hLm.prod MeasurableSet.univ) ?_
    rintro ⟨y, z⟩ ⟨⟨hy, -⟩, hn⟩
    have hz : z ∉ tsupport φ := fun h => hn ⟨hy, h⟩
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  have h3 : ∀ z, ∫ y in (L : Set X), e x y * f y * (e y z * φ z) ∂μ = γ * (g (x + z) * φ z) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hsL : s (x + z) ∈ L := hKL (Or.inr ⟨x + z, ⟨z, hzt, rfl⟩, rfl⟩)
      have hpt : ∀ y, e x y * f y * (e y z * φ z) = φ z * g (x + z) * f (y + s (x + z)) := by
        intro y
        have hexy : e x y * e y z = e y (x + z) := by
          rw [he.symm y (x + z), he.add, he.symm z y]
        rw [mul_assoc (φ z), ← hfg y (x + z), ← hexy]; ring
      simp_rw [hpt]
      rw [integral_const_mul, setIntegral_addSubgroup_add_right μ L hLo f hsL, hLγ]; ring
  rw [h1, integral_integral_swap hint]
  simp_rw [h3]
  rw [integral_const_mul]

end GlobalTheory.KSp.WeilFormula
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Euler

variable {E : Type} [Field E] [NumberField E]

def iota (a : OF E) : Af E := algebraMap E (Af E) (algebraMap (OF E) E a)

def LocIn (n : ℕ) (v : HeightOneSpectrum (OF E)) (z : Af E) : Prop :=
  ∃ a : OF E, ∀ P, Over P v → Valued.v (z P - iota a P) ≤ WithZero.exp (-(n : ℤ))

theorem iota_mul (a b : OF E) : iota (a * b) = iota a * iota b := by simp [iota]

theorem iota_sub (a b : OF E) : iota (a - b) = iota a - iota b := by simp [iota]

theorem iota_add (a b : OF E) : iota (a + b) = iota a + iota b := by simp [iota]

theorem iota_one : iota (1 : OF E) = 1 := by simp [iota]

theorem iota_zero : iota (0 : OF E) = 0 := by simp [iota]

theorem mul_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z * z') P = z P * z' P := rfl

theorem sub_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z - z') P = z P - z' P := rfl

theorem add_coord (z z' : Af E) (P : HeightOneSpectrum (𝓞 E)) : (z + z') P = z P + z' P := rfl

theorem one_coord (P : HeightOneSpectrum (𝓞 E)) : (1 : Af E) P = 1 := rfl

theorem zero_coord (P : HeightOneSpectrum (𝓞 E)) : (0 : Af E) P = 0 := rfl

theorem inv_coord (y : (Af E)ˣ) (P : HeightOneSpectrum (𝓞 E)) : ((y⁻¹ : (Af E)ˣ) : Af E) P = ((y : Af E) P)⁻¹ :=
  eq_inv_of_mul_eq_one_left (coord P y).inv_val

theorem val_iota_le_iff (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : OF E) :
    Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ n := by
  have : iota a = algebraMap E (Af E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  rw [this, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact P.intValuation_le_pow_iff_mem _ n

theorem val_iota_le_one (P : HeightOneSpectrum (𝓞 E)) (a : OF E) : Valued.v (iota a P) ≤ 1 := by
  simpa using (val_iota_le_iff P 0 a).2 (by simp)

theorem val_iota_le_of_mem {P : HeightOneSpectrum (𝓞 E)} {v : HeightOneSpectrum (OF E)} (h : Over P v) (n : ℕ) {a : OF E}
    (ha : a ∈ v.asIdeal ^ n) : Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [val_iota_le_iff]
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) (v.asIdeal ^ n) ≤ P.asIdeal ^ n := by
    rw [Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ n
    rw [Ideal.map_le_iff_le_comap]
    exact h.ge
  exact h1 (Ideal.mem_map_of_mem _ ha)

theorem over_iff_under (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Over P v ↔ P.under (OF E) = v :=
  ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [← h]; rfl⟩

theorem over_under (P : HeightOneSpectrum (𝓞 E)) : Over P (P.under (OF E)) := rfl

theorem mem_aboveF (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) :
    P ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v ↔ Over P v := by
  unfold Formalism.L2.Host.aboveF
  rw [Set.Finite.mem_toFinset, over_iff_under]
  rfl

theorem LocIn.mono {m n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) (hm : m ≤ n) : LocIn m v z := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun P hP => (ha P hP).trans (WithZero.exp_le_exp.2 (by omega))⟩

theorem LocIn.val_le {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E} (h : LocIn n v z) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := h.mono (Nat.zero_le n)
  have h1 : Valued.v (z P - iota a P) ≤ 1 := by simpa using ha P hP
  have := Valuation.map_add_le _ h1 (val_iota_le_one P a)
  rwa [sub_add_cancel] at this

theorem locIn_zero_iff {v : HeightOneSpectrum (OF E)} {z : Af E} : LocIn 0 v z ↔ ∀ P, Over P v → Valued.v (z P) ≤ 1 :=
  ⟨fun h _ hP => h.val_le hP, fun h => ⟨0, fun P hP => by simpa [iota_zero, zero_coord] using h P hP⟩⟩

theorem locIn_congr {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : ∀ P, Over P v → z P = z' P) :
    LocIn n v z ↔ LocIn n v z' :=
  exists_congr fun _ => forall₂_congr fun P hP => by rw [h P hP]

theorem locIn_of_sub_one {n : ℕ} {v : HeightOneSpectrum (OF E)} {z : Af E}
    (h : ∀ P, Over P v → Valued.v (z P - 1) ≤ WithZero.exp (-(n : ℤ))) : LocIn n v z :=
  ⟨1, fun P hP => by rw [iota_one]; exact h P hP⟩

theorem LocIn.mul {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : LocIn n v z) (h' : LocIn n v z') :
    LocIn n v (z * z') := by
  have hz := fun P hP => h.val_le (P := P) hP
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  refine ⟨a * b, fun P hP => ?_⟩
  have : (z * z') P - iota (a * b) P = z P * (z' P - iota b P) + (z P - iota a P) * iota b P := by
    rw [iota_mul, mul_coord, mul_coord]; ring
  rw [this]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul]; exact (mul_le_mul' (hz P hP) (hb P hP)).trans_eq (one_mul _)
  · rw [map_mul]; exact (mul_le_mul' (ha P hP) (val_iota_le_one P b)).trans_eq (mul_one _)

theorem LocIn.inv {n : ℕ} {v : HeightOneSpectrum (OF E)} {y : (Af E)ˣ} (h : LocIn n v y)
    (hu : ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) : LocIn n v (y⁻¹ : (Af E)ˣ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact locIn_zero_iff.2 fun P hP => by rw [inv_coord, map_inv₀, hu P hP, inv_one]
  obtain ⟨a, ha⟩ := h
  by_cases hav : a ∈ v.asIdeal
  · refine ⟨0, fun P hP => absurd (hu P hP) (ne_of_lt ?_)⟩
    have h1 := val_iota_le_of_mem hP 1 (a := a) (by simpa using hav)
    have h2 := (ha P hP).trans (WithZero.exp_le_exp.2 (show -(n : ℤ) ≤ -((1 : ℕ) : ℤ) by omega))
    have := Valuation.map_add_le _ h2 h1
    rw [sub_add_cancel] at this
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hco : IsCoprime (Ideal.span {a}) (v.asIdeal ^ n) := by
    refine IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    exact v.isMaximal.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hav (h.ge (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))))
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hco
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  refine ⟨b, fun P hP => ?_⟩
  have h0 : (y : Af E) P ≠ 0 := (coord P y).ne_zero
  have h1 : iota b P * iota a P + iota t P = 1 := by
    rw [← mul_coord, ← add_coord, ← iota_mul, ← iota_add, hst, iota_one, one_coord]
  have : ((y⁻¹ : (Af E)ˣ) : Af E) P - iota b P =
      ((y : Af E) P)⁻¹ * (iota t P - iota b P * ((y : Af E) P - iota a P)) := by
    rw [inv_coord]; field_simp; linear_combination -h1
  rw [this, map_mul, map_inv₀, hu P hP, inv_one, one_mul]
  refine Valuation.map_sub_le _ (val_iota_le_of_mem hP n ht) ?_
  rw [map_mul]; exact (mul_le_mul' (val_iota_le_one P b) (ha P hP)).trans_eq (one_mul _)

theorem locIn_of_mem_hatO {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (v : HeightOneSpectrum (OF E)) :
    LocIn (expIn c v) v z := by
  obtain ⟨a, ha⟩ := OrderUnits.exists_cong v (expIn c v) (pow_multiplicity_dvd _ _) _
    (fun P hP => (mem_aboveF P v).1 hP) hz
  exact ⟨a, fun P hP => by rw [Valuation.map_sub_swap]; exact ha P ((mem_aboveF P v).2 hP)⟩

end GlobalTheory.CMVal.Euler
end
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.constantPDivGroup_omega_trivial_hodgeTate_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, IsConst G → Subsingleton G.omega ∧ ∀ (h : ℕ) (b : Module.Basis (Fin h) ℤ_[p] G.Tate), Function.Bijective (Fintype.linearCombination O fun i => hodgeTate G (b i)) := by
  first | exact @GlobalTheory.ConstHT.omega_const | exact GlobalTheory.ConstHT.omega_const | (intros; apply GlobalTheory.ConstHT.omega_const <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime]

theorem projective_La_int (D : Datum p) :
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    Module.Projective (𝓞 D.F) D.La := by
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  have htor : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have ha0 : (a : 𝓞 D.F) ≠ 0 := nonZeroDivisors.ne_zero a.2
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) ha0 (Ideal.mem_span_singleton_self (a : 𝓞 D.F))
      (Algebra.IsIntegral.isIntegral (R := ℤ) (a : 𝓞 D.F))
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at he
    obtain ⟨d, hd⟩ := he
    have h1 : e • x = 0 := by
      have : (algebraMap ℤ (𝓞 D.F) e) • x = e • x := by
        rw [algebraMap_smul]
      rw [← this, ← hd, mul_smul]
      change d • (a • x) = 0
      rw [hax, smul_zero]
    rcases smul_eq_zero.1 h1 with h | h
    · exact absurd h he0
    · exact (Submodule.mem_bot _).2 h
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 D.F) D.La
  have : Module.Flat (𝓞 D.F) D.La := (IsDedekindDomain.flat_iff_torsion_eq_bot).2 htor
  have := Module.finitePresentation_of_finite (𝓞 D.F) D.La
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.UPel.HT.EtLev
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.SplitIdem

theorem isCoprime_deriv {p : ℕ} (hp : p.Prime) {t n ρ : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) : IsCoprime (2 * ρ - t) (p : ℤ) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  refine ((hp'.irreducible.coprime_iff_not_dvd).mpr ?_).symm
  intro h2
  apply hd
  have : t ^ 2 - 4 * n = (2 * ρ - t) * (2 * ρ - t) - 4 * (ρ ^ 2 - t * ρ + n) := by ring
  rw [this]
  exact dvd_sub (h2.mul_right _) (h.mul_left _)

theorem exists_root_pow {p : ℕ} (hp : p.Prime) {t n : ℤ} (hd : ¬ (p : ℤ) ∣ t ^ 2 - 4 * n)
    (h : ∃ ρ : ℤ, (p : ℤ) ∣ ρ ^ 2 - t * ρ + n) (k : ℕ) :
    ∃ ρ : ℤ, (p : ℤ) ^ (k + 1) ∣ ρ ^ 2 - t * ρ + n := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    obtain ⟨ρ, c, hc⟩ := ih
    have h1 : (p : ℤ) ∣ ρ ^ 2 - t * ρ + n := by
      rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero k)).mul_right _
    obtain ⟨a, b, hab⟩ := isCoprime_deriv hp hd h1
    refine ⟨ρ - (p : ℤ) ^ (k + 1) * c * a, c * b + (p : ℤ) ^ k * c ^ 2 * a ^ 2, ?_⟩
    linear_combination hc - (p : ℤ) ^ (k + 1) * c * hab

theorem exists_conj_idem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℕ), ∃ ε u v : 𝓞 D.F,
    ε + D.bar ε = 1 + (p : 𝓞 D.F) ^ r * u ∧ ε * D.bar ε = (p : 𝓞 D.F) ^ r * v := by
  intro p hp D r
  obtain ⟨ρ, c, hc⟩ := exists_root_pow hp.out D.disc_p D.split r
  have h1 : (p : ℤ) ∣ ρ ^ 2 - D.tr * ρ + D.nm := by
    rw [hc]; exact (dvd_pow_self _ (Nat.succ_ne_zero r)).mul_right _
  obtain ⟨s, b, hsb⟩ := (isCoprime_deriv hp.out D.disc_p h1).pow_right (n := r)
  have hc' := congrArg (Int.cast : ℤ → 𝓞 D.F) hc
  have hsb' := congrArg (Int.cast : ℤ → 𝓞 D.F) hsb
  push_cast at hc' hsb'
  have ht := D.tr_eq
  have hn := D.nm_eq
  refine ⟨(s : 𝓞 D.F) * ((ρ : 𝓞 D.F) - D.ω), -(b : 𝓞 D.F), (s : 𝓞 D.F) ^ 2 * (p : 𝓞 D.F) * (c : 𝓞 D.F), ?_, ?_⟩
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination hsb' - (s : 𝓞 D.F) * ht
  · rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination (s : 𝓞 D.F) ^ 2 * hc' - (s : 𝓞 D.F) ^ 2 * (ρ : 𝓞 D.F) * ht + (s : 𝓞 D.F) ^ 2 * hn

end GlobalTheory.UPel.HT.SplitIdem
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieCoordMult

theorem tanScal_decomp : ∀ (O : Type) [Ring O] (F' : Type) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (act : OActN O G) (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (n a : ℕ) (T : (Fin n → R') → (epsPtR x ⟶ G)) (A : O → Matrix (Fin n) (Fin n) R') (emb : F' → O) (ω : F') (l : R') (χ : Fin a → F' → R'), Function.Injective T → (∀ v : epsPtR x ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : R') c, (T (s • c)).left = spMap (epsScaleR s) ≫ (T c).left) → (∀ b c, T c ≫ act.act b = T (A b *ᵥ c)) → (∀ y : Fin n → R', A (emb ω) *ᵥ y = l • y → ∃ z : Fin a → Fin n → R', (∀ i c, A (emb c) *ᵥ z i = χ i c • z i) ∧ y = ∑ i, z i) → ∀ v : epsPtR x ⟶ G, IsTanScal act x (emb ω) l v → ∃ w : Fin a → (epsPtR x ⟶ G), (∀ i c, IsTanScal act x (emb c) (χ i c) (w i)) ∧ v = (List.ofFn w).prod := by
  intro O _ F' S G _ _ act R' _ x n a T A emb ω l χ hinj htan hadd hsc hact hdec v hv
  have T0 : T 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have Tsum : ∀ (m : ℕ) (y : Fin m → (Fin n → R')), (List.ofFn (fun i => T (y i))).prod = T (∑ i, y i) := by
    intro m
    induction m with
    | zero => intro y; simp [T0]
    | succ m ih => intro y; rw [List.ofFn_succ, List.prod_cons, ih, Fin.sum_univ_succ, hadd]
  have eig : ∀ (b : O) (c : R') (w : epsPtR x ⟶ G), IsTanScal act x b c w ↔ ∃ y, A b *ᵥ y = c • y ∧ w = T y := by
    intro b c w
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := (htan w).1 h1
      refine ⟨y, hinj (Over.OverMorphism.ext ?_), rfl⟩
      rw [← hact, h2, hsc]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(htan _).2 ⟨y, rfl⟩, ?_⟩
      rw [hact, hy, hsc]
  obtain ⟨y, hy, rfl⟩ := (eig _ _ _).1 hv
  obtain ⟨z, hz, rfl⟩ := hdec y hy
  exact ⟨fun i => T (z i), fun i c => (eig _ _ _).2 ⟨z i, hz i c, rfl⟩, (Tsum a z).symm⟩

end GlobalTheory.LieCoordMult
end
end

section

open scoped NumberField

theorem _root_.GlobalTheory.T.card_lTorsion_eq_pow_of_tateSimilitude : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  first | (exact @GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (exact GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (exact GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (intros; apply GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.oLinear_of_basis_products_additive_points : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  first | (exact @GlobalTheory.basisLin_oLinear) | (exact GlobalTheory.basisLin_oLinear) | (intros; apply GlobalTheory.basisLin_oLinear  <;> assumption)
end

section

open NumberField


theorem _root_.GlobalTheory.T.charpoly_la_eq_pow (p : ℕ) [Fact p.Prime]
    (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F) :
    haveI := D.freeLa
    haveI := D.finLa
    LinearMap.charpoly (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) :=
  GlobalTheory.UPel.HT.Datum.charpoly_La_eq_pow p D c
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.grpObj_tangentVector_add_at_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S) (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left → ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left → wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  first | (exact @GlobalTheory.GrpTangentPt.tanadd) | (exact GlobalTheory.GrpTangentPt.tanadd) | (intros; apply GlobalTheory.GrpTangentPt.tanadd  <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylorOrder_traceForm_nondegenerate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (x : D.O), (∀ y : D.O, LinearMap.trace ℤ D.O (LinearMap.mulLeft ℤ (x * y)) = 0) → x = 0 := by
  first | exact @GlobalTheory.HTOrderTrace.trace_order_nondeg | exact GlobalTheory.HTOrderTrace.trace_order_nondeg | (intros; apply GlobalTheory.HTOrderTrace.trace_order_nondeg <;> assumption)
end
