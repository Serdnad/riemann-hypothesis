module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.CintIdx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.NotEvenIrr
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle014
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle069
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

namespace UpperTheory.HilbertUnitGroup

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {τ : K}

private theorem mem_ord {y w : Etau K τ} :
    w ∈ Ord O y ↔ ∃ a b : O, w = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y := by
  change w ∈ Submodule.span O {1, y} ↔ _
  rw [Submodule.mem_span_pair]
  simp only [Algebra.smul_def, mul_one, eq_comm]

private theorem ord_mul {y v w : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hv : v ∈ Ord O y) (hw : w ∈ Ord O y) : v * w ∈ Ord O y := by
  obtain ⟨a, b, rfl⟩ := mem_ord.1 hv
  obtain ⟨a', b', rfl⟩ := mem_ord.1 hw
  refine mem_ord.2 ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
  simp only [map_add (f := _), map_mul]
  linear_combination (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy

private theorem mem_Hu {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c) {u : (Etau K τ)ˣ} :
    u ∈ Hu O y ↔ (u : Etau K τ) ∈ Ord O y ∧ ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := by
  have one : (1 : Etau K τ) ∈ Ord O y := mem_ord.2 ⟨1, 0, by simp⟩
  have key : ∀ v : (Etau K τ)ˣ, v ∈ Hu O y → ((v⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O y := fun v hv => by
    have h1 : (1 : Etau K τ) ∈ PS.ml v (Ord O y) := by
      rw [show PS.ml v (Ord O y) = Ord O y from hv]; exact one
    simpa using PS.mem_ml.1 h1
  refine ⟨fun h => ⟨by simpa using key _ (inv_mem h), key _ h⟩, fun ⟨h1, h2⟩ => ?_⟩
  change PS.ml u (Ord O y) = Ord O y
  ext w
  rw [PS.mem_ml]
  refine ⟨fun hw => ?_, fun hw => ord_mul hy h2 hw⟩
  simpa using ord_mul hy h1 hw

private theorem uniq (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {a b a' b' : O}
    (h : algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y =
      algebraMap O (Etau K τ) a' + algebraMap O (Etau K τ) b' * y) : a = a' ∧ b = b' := by
  rw [algebraMap_etau a, algebraMap_etau b, algebraMap_etau a', algebraMap_etau b'] at h
  have im_algebraMap_add_mul : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).im = q * y.im := by
    intro p q; simp
  have kre : ∀ p q : K, (algebraMap K (Etau K τ) p + algebraMap K (Etau K τ) q * y).re = p + q * y.re := by
    intro p q; simp
  have him := congrArg QuadraticAlgebra.im h
  have hre := congrArg QuadraticAlgebra.re h
  rw [im_algebraMap_add_mul, im_algebraMap_add_mul] at him
  rw [kre, kre] at hre
  have hb := mul_right_cancel₀ h0 him
  rw [hb] at hre
  exact ⟨hinj (add_right_cancel hre), hinj hb⟩

private theorem isUnit_fst (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c : O}
    (hy : y * y = algebraMap O (Etau K τ) c) (hc : ¬ IsUnit c) {u : (Etau K τ)ˣ} (hu : u ∈ Hu O y) {a b : O}
    (e : (u : Etau K τ) = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y) : IsUnit a := by
  obtain ⟨a', b', e'⟩ := mem_ord.1 ((mem_Hu hy).1 hu).2
  have h1 : algebraMap O (Etau K τ) (a * a' + b * b' * c) + algebraMap O (Etau K τ) (a * b' + a' * b) * y =
      algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) 0 * y := by
    have := u.mul_inv
    rw [e, e'] at this
    simp only [map_add (f := _), map_mul, map_one, map_zero]
    linear_combination this - (algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) b') * hy
  have h2 := (uniq hinj h0 h1).1
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h2 with h3 | h3
  · exact isUnit_of_mul_isUnit_left h3
  · exact absurd (isUnit_of_mul_isUnit_right h3) hc

private theorem step (hinj : Function.Injective (algebraMap O K)) {y : Etau K τ} (h0 : y.im ≠ 0) {c π : O}
    (hπ : Irreducible π) (hy : y * y = algebraMap O (Etau K τ) c) (hc : π ∣ c) :
    (Hu O (algebraMap O (Etau K τ) π * y)).relIndex (Hu O y) = Nat.card (IsLocalRing.ResidueField O) := by
  classical
  have hcu : ¬ IsUnit c := fun h => hπ.not_isUnit (isUnit_of_dvd_unit hc h)
  have hy' : (algebraMap O (Etau K τ) π * y) * (algebraMap O (Etau K τ) π * y) =
      algebraMap O (Etau K τ) (π * π * c) := by
    simp only [map_mul]; linear_combination (algebraMap O (Etau K τ) π * algebraMap O (Etau K τ) π) * hy
  have hπ0 : IsLocalRing.residue O π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
  have hc0 : IsLocalRing.residue O c = 0 := by
    obtain ⟨d, rfl⟩ := hc; rw [map_mul, hπ0, zero_mul]
  have ex : ∀ u : Hu O y, ∃ p : O × O, ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) p.1 + algebraMap O (Etau K τ) p.2 * y := fun u => by
    obtain ⟨a, b, e⟩ := mem_ord.1 ((mem_Hu hy).1 u.2).1
    exact ⟨(a, b), e⟩
  choose P hP using ex
  let g : Hu O y → IsLocalRing.ResidueField O := fun u =>
    IsLocalRing.residue O (P u).2 / IsLocalRing.residue O (P u).1
  have gval : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y →
      g u = IsLocalRing.residue O b / IsLocalRing.residue O a := fun u a b e => by
    obtain ⟨h1, h2⟩ := uniq hinj h0 ((hP u).symm.trans e)
    simp only [g, h1, h2]
  have resne : ∀ (u : Hu O y) (a b : O), ((u : (Etau K τ)ˣ) : Etau K τ) =
      algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * y → IsLocalRing.residue O a ≠ 0 := fun u a b e =>
    ((isUnit_fst hinj h0 hy hcu u.2 e).map (IsLocalRing.residue O)).ne_zero
  have gmul : ∀ u v : Hu O y, g (u * v) = g u + g v := fun u v => by
    have eu := hP u
    have ev := hP v
    have e : (((u * v : Hu O y) : (Etau K τ)ˣ) : Etau K τ) =
        algebraMap O (Etau K τ) ((P u).1 * (P v).1 + (P u).2 * (P v).2 * c) +
          algebraMap O (Etau K τ) ((P u).1 * (P v).2 + (P v).1 * (P u).2) * y := by
      rw [Subgroup.coe_mul, Units.val_mul, eu, ev]
      simp only [map_add (f := _), map_mul]
      linear_combination (algebraMap O (Etau K τ) (P u).2 * algebraMap O (Etau K τ) (P v).2) * hy
    have n1 := resne u _ _ eu
    have n2 := resne v _ _ ev
    rw [gval _ _ _ e, gval _ _ _ eu, gval _ _ _ ev]
    simp only [map_add (f := _), map_mul, hc0, mul_zero, add_zero]
    field_simp
    ring
  let f : Hu O y →* Multiplicative (IsLocalRing.ResidueField O) :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (g u)) (fun u v => by rw [gmul, ofAdd_add])
  have fval : ∀ u, f u = Multiplicative.ofAdd (g u) := fun _ => rfl
  have down : ∀ u : Hu O y, f u = 1 → ((u : (Etau K τ)ˣ) : Etau K τ) ∈ Ord O (algebraMap O (Etau K τ) π * y) := fun u hu => by
    have h1 : g u = 0 := by simpa [fval] using hu
    have e := hP u
    rw [gval _ _ _ e, div_eq_zero_iff, or_iff_left (resne u _ _ e), IsLocalRing.residue_eq_zero_iff,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨d, hd⟩ := h1
    refine mem_ord.2 ⟨(P u).1, d, ?_⟩
    rw [e, hd, map_mul]
    ring
  have hker : f.ker = (Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Hu hy']
    refine ⟨fun hu => ⟨down u hu, ?_⟩, fun ⟨h1, _⟩ => ?_⟩
    · have := down u⁻¹ (by rw [map_inv, hu, inv_one])
      simpa using this
    · obtain ⟨a, b, e⟩ := mem_ord.1 h1
      have e' : ((u : (Etau K τ)ˣ) : Etau K τ) =
          algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) (b * π) * y := by
        rw [e, map_mul]; ring
      rw [fval, gval _ _ _ e', map_mul, hπ0, mul_zero, zero_div, ofAdd_zero]
  have hsurj : Function.Surjective f := fun r => by
    obtain ⟨s, hs⟩ := IsLocalRing.residue_surjective (Multiplicative.toAdd r)
    have hn : IsUnit (1 - s * s * c) := by
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (a := 1 - s * s * c) (b := s * s * c) (by ring) with h | h
      · exact h
      · exact absurd (isUnit_of_mul_isUnit_right h) hcu
    obtain ⟨ν, hν⟩ := hn
    have hν' : algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * (1 - algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) c) = 1 := by
      rw [← map_mul, ← map_mul, ← map_one (algebraMap O (Etau K τ)), ← map_sub, ← hν, ← map_mul, Units.inv_mul]
    let w : (Etau K τ)ˣ :=
      { val := algebraMap O (Etau K τ) 1 + algebraMap O (Etau K τ) s * y
        inv := algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) + algebraMap O (Etau K τ) (-(((ν⁻¹ : Oˣ) : O) * s)) * y
        val_inv := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy
        inv_val := by
          simp only [map_neg, map_mul, map_one]
          linear_combination hν' - (algebraMap O (Etau K τ) ((ν⁻¹ : Oˣ) : O) * algebraMap O (Etau K τ) s * algebraMap O (Etau K τ) s) * hy }
    have hw : w ∈ Hu O y := (mem_Hu hy).2 ⟨mem_ord.2 ⟨1, s, rfl⟩, mem_ord.2 ⟨_, _, rfl⟩⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    rw [fval, gval ⟨w, hw⟩ 1 s rfl, map_one, div_one, hs, ofAdd_toAdd]
  have hr : f.range = ⊤ := MonoidHom.range_eq_top.2 hsurj
  change ((Hu O (algebraMap O (Etau K τ) π * y)).subgroupOf (Hu O y)).index = _
  rw [← hker, Subgroup.index_ker, hr, Subgroup.card_top]
  exact Nat.card_congr Multiplicative.toAdd

end UpperTheory.HilbertUnitGroup

theorem UpperTheory.relIndex_stabilizer_succ_eq_card_residueField :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ m : ℕ, 1 ≤ m → (Hu O (yy π (m + 1) x)).relIndex (Hu O (yy π m x)) = Nat.card (IsLocalRing.ResidueField O) := by
  intro O K _ _ _ _ _ Δ τ L _ π n e h x hC m hm
  haveI := L.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ := hC.irr
  have hp : algebraMap O K (π ^ m) ≠ 0 := fun h0 =>
    pow_ne_zero m hπ.ne_zero (hinj (by rw [h0, map_zero]))
  have h0 : (yy π m x).im ≠ 0 := by
    rw [yy, im_smul, smul_eq_mul]
    exact mul_ne_zero hp hC.gen.im_ne
  have hsm : ∀ k : ℕ, yy π k x = algebraMap O (Etau K τ) (π ^ k) * x := fun k => by
    rw [yy, Algebra.smul_def, ← algebraMap_etau]
  have hy : yy π m x * yy π m x = algebraMap O (Etau K τ) (π ^ m * π ^ m * (e : O)) := by
    rw [hsm, map_mul, map_mul, ← hC.sq]; ring
  have hc : π ∣ π ^ m * π ^ m * (e : O) :=
    Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_pow_self π (by omega)) _) _
  have e1 : yy π (m + 1) x = algebraMap O (Etau K τ) π * yy π m x := by
    rw [hsm, hsm, pow_succ, map_mul]; ring
  rw [e1]
  exact UpperTheory.HilbertUnitGroup.step hinj h0 hπ hy hc
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem ord_mem {y z : Etau K τ} :
    z ∈ PK.Ord (O := O) y ↔ ∃ a b : O, a • (1 : Etau K τ) + b • y = z :=
  Submodule.mem_span_pair

private theorem ord_one (y : Etau K τ) : (1 : Etau K τ) ∈ PK.Ord (O := O) y :=
  ord_mem.2 ⟨1, 0, by simp⟩

private theorem ord_mul {y : Etau K τ} {c : O} (hy : y * y = algebraMap O (Etau K τ) c)
    {z z' : Etau K τ} (hz : z ∈ PK.Ord (O := O) y) (hz' : z' ∈ PK.Ord (O := O) y) : z * z' ∈ PK.Ord (O := O) y := by
  obtain ⟨a, b, rfl⟩ := ord_mem.1 hz
  obtain ⟨p, q, rfl⟩ := ord_mem.1 hz'
  refine ord_mem.2 ⟨a * p + b * q * c, a * q + b * p, ?_⟩
  simp only [Algebra.smul_def, map_add (f := _), map_mul]
  linear_combination (-(algebraMap O (Etau K τ) b * algebraMap O (Etau K τ) q)) * hy

private theorem ord_sub {y y' : Etau K τ} {c c' : O} (hy : y * y = algebraMap O (Etau K τ) c)
    (hy' : y' * y' = algebraMap O (Etau K τ) c') {w : (Etau K τ)ˣ}
    (hw : PS.ml w (PK.Ord (O := O) y) = PK.Ord (O := O) y') {z : Etau K τ} (hz : z ∈ PK.Ord (O := O) y) : z ∈ PK.Ord (O := O) y' := by
  have hw1 : ((w⁻¹ : (Etau K τ)ˣ) : Etau K τ) ∈ PK.Ord (O := O) y := by
    have := ord_one (O := O) y'
    rw [← hw, PS.mem_ml, mul_one] at this
    exact this
  rw [← hw, PS.mem_ml]
  exact ord_mul hy hw1 hz
end

private theorem lvl_le {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {τ : K} {π : O} (hπ : Irreducible π) {x : Etau K τ}
    (hx : x.im ≠ 0) {m m' : ℕ} (h : yy π m x ∈ PK.Ord (O := O) (yy π m' x)) : m' ≤ m := by
  obtain ⟨a, b, hab⟩ := ord_mem.1 h
  have him := congrArg QuadraticAlgebra.im hab
  simp only [yy, ← algebraMap_smul K a, ← algebraMap_smul K b, im_add, im_smul, im_one, mul_zero, zero_add,
    smul_eq_mul] at him
  have hk : algebraMap O K (b * π ^ m') = algebraMap O K (π ^ m) := by
    rw [map_mul]
    exact mul_right_cancel₀ hx (by rw [← him]; ring)
  have hd : π ^ m' ∣ π ^ m := ⟨b, by rw [IsFractionRing.injective O K hk.symm, mul_comm]⟩
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 hd

theorem UpperTheory.order_level_injective_of_smul_eq :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (w : (Etau K τ)ˣ) (m m' : ℕ), PS.ml w (PK.Ord (O := O) (yy π m x)) = PK.Ord (O := O) (yy π m' x) → m = m' := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc w m m' hw
  haveI := L.frac
  have hx : x.im ≠ 0 := hc.gen.im_ne
  have hsq : ∀ j : ℕ, yy π j x * yy π j x = algebraMap O (Etau K τ) (π ^ j * π ^ j * e) := by
    intro j
    simp only [yy, smul_mul_smul_comm, hc.sq]
    rw [IsScalarTower.algebraMap_apply O K (Etau K τ), IsScalarTower.algebraMap_apply O K (Etau K τ),
      Algebra.smul_def, ← map_mul, map_mul (algebraMap O K) (π ^ j * π ^ j), map_mul (algebraMap O K) (π ^ j)]
  have self_mem : ∀ j : ℕ, yy π j x ∈ PK.Ord (O := O) (yy π j x) := fun j => ord_mem.2 ⟨0, 1, by simp⟩
  have hw' : PS.ml w⁻¹ (PK.Ord (O := O) (yy π m' x)) = PK.Ord (O := O) (yy π m x) := by
    rw [← hw, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
  have h1 : m' ≤ m := lvl_le hc.irr hx (ord_sub (hsq m) (hsq m') hw (self_mem m))
  have h2 : m ≤ m' := lvl_le hc.irr hx (ord_sub (hsq m') (hsq m) hw' (self_mem m'))
  omega
end

section

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

theorem UpperTheory.ncard_unit_translates_order_eq_relIndex :
    ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (τ : K) (a : (Etau K τ)ˣ) (y : Etau K τ), {S : Set (Etau K τ) | ∃ u ∈ Gu O τ, S = PS.ml (a * u) (Ord O y)}.ncard = (Hu O y).relIndex (Gu O τ) := by
  intro O K _ _ _ τ a y
  set G := Gu O τ
  set H := (Hu O y).subgroupOf G
  have key : ∀ g₁ g₂ : G, PS.ml (a * (g₁ : (Etau K τ)ˣ)) (PK.Ord O y) =
      PS.ml (a * (g₂ : (Etau K τ)ˣ)) (PK.Ord O y) ↔ g₁⁻¹ * g₂ ∈ H := by
    intro g₁ g₂
    rw [Subgroup.mem_subgroupOf]
    show _ ↔ PS.ml (((g₁⁻¹ * g₂ : G)) : (Etau K τ)ˣ) (PK.Ord O y) = PK.Ord O y
    rw [PS.ml_mul, PS.ml_mul, (PS.ml_inj a).eq_iff, Subgroup.coe_mul, Subgroup.coe_inv, PS.ml_mul]
    constructor
    · intro h
      rw [← h, ← PS.ml_mul, inv_mul_cancel, PS.ml_one]
    · intro h
      conv_lhs => rw [← h]
      rw [← PS.ml_mul, mul_inv_cancel, PS.ml_one]
  let f : G ⧸ H → Set (Etau K τ) :=
    Quotient.lift (fun g : G => PS.ml (a * (g : (Etau K τ)ˣ)) (PK.Ord O y))
      (fun g₁ g₂ hg => (key g₁ g₂).2 (QuotientGroup.leftRel_apply.1 hg))
  have hf : Function.Injective f := by
    intro q₁ q₂ hq
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    exact QuotientGroup.eq.2 ((key _ _).1 hq)
  have hrange : {S : Set (Etau K τ) | ∃ u ∈ G, S = PS.ml (a * u) (PK.Ord O y)} = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨((⟨u, hu⟩ : G) : G ⧸ H), rfl⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨g, g.2, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hf]
  rfl
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_normV_eq_prime_pow_le_finrank :
    ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ∃ h : ℕ, 1 ≤ h ∧ h ≤ Module.finrank ℚ K ∧ normV w = p ^ h := by
  intro K _ _ p w hp hpw
  have hcard : normV w = Ideal.absNorm w.asIdeal := by
    unfold normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hdvd : Ideal.absNorm w.asIdeal ∣ p ^ Module.finrank ℚ K := by
    rw [← hspan]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpw)
  obtain ⟨h, hle, heq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨h, ?_, hle, hcard.trans heq⟩
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · exfalso
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at heq
    exact w.isPrime.ne_top heq
  · exact h0
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.adicNorm_prod_le_prod_of_injective_classes :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (O S R : Type) [Fintype O] [Fintype S] (f : O → S → ℂ), (∀ o s, IsIntegral ℤ (f o s)) → ∀ (X : O → Finset R) (cl : ∀ o, ↥(X o) → S), (∀ o, Function.Injective (cl o)) → ‖ι.symm (∏ o, ∏ s, f o s)‖ ≤ ∏ o, ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖ := by
  intro l _ ι O S R _ _ f hf X cl hcl
  classical
  have h1 : ∀ o s, ‖ι.symm (f o s)‖ ≤ 1 := fun o s =>
    GlobalTheory.norm_le_one_of_isIntegral_int (map_isIntegral_int ι.symm (hf o s))
  rw [map_prod, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun o _ => ?_)
  rw [map_prod, norm_prod]
  have h2 : ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖
      = ∏ s ∈ Finset.univ.map ⟨cl o, hcl o⟩, ‖ι.symm (f o s)‖ := by
    rw [Finset.prod_map]; rfl
  rw [h2]
  exact Finset.prod_le_prod_of_subset_of_le_one₀ (Finset.subset_univ _)
    (fun _ _ => norm_nonneg _) (fun s _ _ => h1 o s)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

private theorem pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qh11.pow_cong A ha hb h m

private theorem dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) : IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n) (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

private theorem dec_lt {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {g : G K Ω}
    (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x < 1) : A.valuation (g x) < 1 := by
  by_contra hc
  have h1 : 1 ≤ A.valuation (g x) := not_lt.1 hc
  have h2 : A.valuation (g x⁻¹) ≤ 1 := by
    rw [map_inv₀, map_inv₀]
    exact inv_le_one_of_one_le₀ h1
  have h3 := dec_le (inv_mem hg) h2
  have e : g⁻¹ (g x⁻¹) = x⁻¹ := g.symm_apply_apply _
  rw [e, map_inv₀] at h3
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h1
  have h0 : 0 < A.valuation x := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx0)
  exact absurd hx (not_lt.2 ((inv_le_one₀ h0).1 h3))

private theorem inv_mul_ine {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω} {q : ℕ}
    {g h : G K Ω} (hg : IsFrob (F := K) A q g) (hh : IsFrob (F := K) A q h) : h⁻¹ * g ∈ Ine (F := K) A := by
  refine ⟨mul_mem (inv_mem hh.1) hg.1, fun x hx => ?_⟩
  have h3 := Valuation.map_sub_lt A.valuation (hg.2 _ hx) (hh.2 _ hx)
  rw [sub_sub_sub_cancel_right] at h3
  have h4 := dec_lt (inv_mem hh.1) h3
  have e : h⁻¹ (h x) = x := h.symm_apply_apply x
  rw [map_sub, e] at h4
  exact h4

private theorem asIdeal_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  have hpr : Prime (p : 𝓞 ℚ) := by
    have h : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).mpr hpr).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  exact (hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)).symm

private theorem normV_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    normV v = p := by
  have h : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h, asIdeal_eq hp v hv, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

theorem UpperTheory.frobenius_pow_resDeg_place_norm :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] (p h : ℕ) (w : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → (p : 𝓞 ℚ) ∈ v.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B w → ∀ σ : G K Ω, IsFrob B (p ^ h) σ → IsPlaceOver B v ∧ ∃ τ : G ℚ Ω, IsFrob B (normV v) τ ∧ (τ ^ h)⁻¹ * σ.restrictScalars ℚ ∈ Ine (F := ℚ) B := by
  intro K Ω _ _ _ _ _ _ _ p h w v hp hw hv B hB σ hσ
  have hcl : IsAlgClosure ℚ Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed K
      isAlgebraic := Algebra.IsAlgebraic.trans ℚ K Ω }
  have hu : (p : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    show algebraMap (𝓞 ℚ) (𝓞 K) (p : 𝓞 ℚ) ∈ w.asIdeal
    rwa [map_natCast]
  have hvw : v = w.under (𝓞 ℚ) :=
    HeightOneSpectrum.ext ((asIdeal_eq hp v hv).trans (asIdeal_eq hp _ hu).symm)
  have hBv : IsPlaceOver B v := by
    rw [hvw]
    intro x
    rw [IsScalarTower.algebraMap_apply ℚ K Ω]
    exact hB (algebraMap (𝓞 ℚ) (𝓞 K) x)
  refine ⟨hBv, ?_⟩
  obtain ⟨τ, hτ⟩ := exists_isFrob hBv
  refine ⟨τ, hτ, ?_⟩
  rw [normV_eq hp v hv] at hτ
  have hσ' : IsFrob (F := ℚ) B (p ^ h) (σ.restrictScalars ℚ) := ⟨hσ.1, hσ.2⟩
  exact inv_mul_ine hσ' (isFrob_pow hτ h)
end
