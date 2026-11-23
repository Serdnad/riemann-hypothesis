module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle007
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MemTwCentConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbSum
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori

private theorem map_diag {E F : Type} [Field E] [Field F] {n : ℕ} (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [val_diagT]
  · simp [val_diagT, Matrix.diagonal_apply, hij]

private theorem diag_comm {E : Type} [Field E] {n : ℕ} (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

private theorem strict_map {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] {n : ℕ} {t : Fin n → kˣ} (ht : Strict t) :
    Strict fun i => Units.map (algebraMap k E : k →* E) (t i) := by
  intro i j hij
  have h := ht i j hij
  rw [← (valuation k).vlt_iff_lt] at h
  rw [← (valuation E).vlt_iff_lt]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  intro hle
  exact h (ValuativeExtension.vle_iff_vle.mp hle)

theorem UpperTheory.Gal.InertialTypesAlt.L.align :
    UpperTheory.Gal.InertialTypesAlt.L.Align := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ h y γ d hd hnorm hy
  obtain ⟨hcyc, -, hb⟩ := bridge k E σ
  obtain ⟨hsg, hnrm, -, -, -⟩ := hb n
  obtain ⟨hND, -, -⟩ := normDiag k E σ hσ n
  obtain ⟨hN, hstr, hreg⟩ := hND d
  have e := nrm_conj hcyc.ord δ y
  rw [hsg y, hy, hnrm, hnrm, hN, hnorm] at e
  set T := diagT k (Fin n) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d) with hTdef
  obtain ⟨z, hz⟩ := conjDesc k E n T γ (hreg hd) ⟨h⁻¹ * y, by rw [e]; group⟩
  refine ⟨z, by rw [hz]; group, ?_⟩
  intro t ht
  have hct : γ * t = t * γ := Subgroup.mem_centralizer_iff.mp ht γ rfl
  set m : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d i) with hm
  have hms : Strict m := strict_map (hstr hd)
  have hT : (incl T : GL (Fin n) E) = diagT E (Fin n) m := map_diag (algebraMap k E) _
  have hrefl : Cyc (RingEquiv.refl E) 1 := ⟨fun x => rfl, one_pos, fun x => rfl⟩
  have hsgr : ∀ g : GL (Fin n) E, sg (RingEquiv.refl E) g = g := by
    intro g
    ext i j
    rfl
  set u := z⁻¹ * t * z with hu
  have huc : u * T = T * u := by
    have hz' : T = z⁻¹ * γ * z := by rw [hz]; group
    rw [hz', hu]
    calc z⁻¹ * t * z * (z⁻¹ * γ * z) = z⁻¹ * (t * γ) * z := by group
      _ = z⁻¹ * (γ * t) * z := by rw [hct]
      _ = z⁻¹ * γ * z * (z⁻¹ * t * z) := by group
  obtain ⟨s2, hs2⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms (incl u) (by
    rw [hsgr, ← hT, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← huc]
    congr 1
    group)
  set w := y⁻¹ * h * incl z with hw
  have hg : (incl γ : GL (Fin n) E) = incl z * incl T * (incl z)⁻¹ := by
    rw [hz]
    simp only [map_mul, map_inv]
  have hwc0 : (incl T : GL (Fin n) E) = w * incl T * w⁻¹ := by
    conv_lhs => rw [e]
    rw [hg, hw]
    group
  have hwc : w⁻¹ * diagT E (Fin n) m * w = diagT E (Fin n) m := by
    rw [← hT]
    conv_lhs => rw [hwc0]
    group
  obtain ⟨s1, hs1⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms w (by rw [hsgr]; exact hwc)
  have ht' : (incl t : GL (Fin n) E) = incl z * incl u * (incl z)⁻¹ := by
    rw [hu]
    simp only [map_mul, map_inv]
    group
  have key : y⁻¹ * (h * incl t * h⁻¹) * y = w * incl u * w⁻¹ := by
    rw [ht', hw]
    group
  rw [key, hs1, hs2, diag_comm]
  group
end

section

open ValuativeRel Matrix Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_rad {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ r < γ := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hc0 : 0 < valuation k x := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)
  have hm0 : 0 < min γ 1 := lt_min (zero_lt_iff.2 hγ) zero_lt_one
  have hlt : valuation k x * min γ 1 < min γ 1 := mul_lt_of_lt_one_left hm0 hx1
  exact ⟨valuation k x * min γ 1, mul_pos hc0 hm0, hlt.trans_le (min_le_right _ _), hlt.trans_le (min_le_left _ _)⟩

private theorem nhds_rad {x : k} {W : Set k} (hW : W ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | valuation k (y - x) ≤ r} ⊆ W := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds' x).mem_iff.1 hW
  obtain ⟨r, h0, h1, h2⟩ := exists_rad hγ
  exact ⟨r, h0, h1, fun y hy => hs (lt_of_le_of_lt hy h2)⟩

private theorem fin_rad {ι : Type} [Finite ι] (R : ι → ValueGroupWithZero k) (h0 : ∀ i, 0 < R i) (h1 : ∀ i, R i < 1) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ i, r ≤ R i := by
  obtain ⟨c, hc0, hc1, -⟩ := exists_rad (k := k) one_ne_zero
  obtain ⟨o, ho⟩ := Finite.exists_min (fun o : Option ι => o.elim c R)
  refine ⟨o.elim c R, ?_, ?_, fun i => ho (some i)⟩
  · cases o with
    | none => exact hc0
    | some i => exact h0 i
  · cases o with
    | none => exact hc1
    | some i => exact h1 i

private theorem pi_rad {ι : Type} [Finite ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (P : ∀ i, ValueGroupWithZero k → Set (X i))
    (hP : ∀ i, ∀ W ∈ 𝓝 (x i), ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ P i r ⊆ W)
    (hm : ∀ i r r', r' ≤ r → P i r' ⊆ P i r) {V : Set (∀ i, X i)} (hV : V ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | ∀ i, y i ∈ P i r} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hsub⟩ := hV
  choose R h0 h1 hR using fun i => hP i (t i) (ht i)
  obtain ⟨r, hr0, hr1, hr⟩ := fin_rad R h0 h1
  exact ⟨r, hr0, hr1, fun y hy => hsub fun i _ => hR i (hm i _ _ (hr i) (hy i))⟩

private theorem mat_rad {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)} (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧
      {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r} ⊆ V := by
  refine pi_rad (X := fun _ : Fin n => Fin n → k) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun i r => {y | ∀ j, valuation k (y j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun i W hW => ?_)
    (fun i r r' h y hy j => (hy j).trans h) hV
  exact pi_rad (X := fun _ : Fin n => k) (fun j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun j r => {y | valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun j W hW => nhds_rad hW)
    (fun j r r' h y hy => (show valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r from le_trans hy h)) hW

private theorem unit_nhds {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∃ V ∈ 𝓝 (1 : A), ∀ g : Aˣ, (g : A) ∈ V → ((g⁻¹ : Aˣ) : A) ∈ V → g ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 (by simpa using hT)
  refine ⟨a ∩ MulOpposite.op ⁻¹' b, Filter.inter_mem ha
    (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hb)), fun g h1 h2 => hTU ?_⟩
  exact hab ⟨h1.1, h2.2⟩

private theorem val_near {r : ValueGroupWithZero k} (h1 : r < 1) {x : k} (hx : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h := Valuation.map_one_add_of_lt (valuation k) (lt_of_le_of_lt hx h1)
  simpa using h

private theorem near_mul' {r : ValueGroupWithZero k} (h1 : r < 1) {x y : k} (hx : valuation k (x - 1) ≤ r)
    (hy : valuation k (y - 1) ≤ r) : valuation k (x * y - 1) ≤ r := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul, val_near h1 hx, one_mul]
  exact hy

private theorem near_inv' {r : ValueGroupWithZero k} (h1 : r < 1) (x : kˣ) (hx : valuation k ((x : k) - 1) ≤ r) :
    valuation k (((x⁻¹ : kˣ) : k) - 1) ≤ r := by
  have hv := val_near h1 hx
  have e : ((x⁻¹ : kˣ) : k) - 1 = -((x : k) - 1) * ((x⁻¹ : kˣ) : k) := by
    rw [neg_mul, sub_mul, Units.mul_inv]
    ring
  have hv' : valuation k ((x⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  rw [e, map_mul, hv', mul_one, Valuation.map_neg]
  exact hx

private theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

private theorem compact_units (r : ValueGroupWithZero k) (h1 : r < 1) :
    IsCompact {x : kˣ | valuation k ((x : k) - 1) ≤ r} := by
  haveI : T2Space k := t2
  have hC : IsCompact {x : k | valuation k (x - 1) ≤ r} := by
    have h := (IsNonarchimedeanLocalField.isCompact_closedBall k r).image (f := fun x => x + 1) (by fun_prop)
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨x - 1, hx, sub_add_cancel _ _⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have h := (Units.isClosedEmbedding_embedProduct (α := k)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    MulOpposite.op_injective.mem_set_image]
  exact ⟨fun hx => ⟨hx, near_inv' h1 x hx⟩, fun hx => hx.1⟩

end SlopeTestRemainingChoices

theorem smallRad :
    UpperTheory.Gal.InertialTypesAlt.L.SmallRad := by
  intro k _ _ _ _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := unit_nhds hU
    obtain ⟨r, h0, h1, hr⟩ := mat_rad hV
    obtain ⟨K, hK, -, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
    refine ⟨r, h0, h1, fun r' hr' g hg => ?_⟩
    have hg' : g ∈ ball n r := fun i j => (hg i j).trans hr'
    have hgK : g ∈ K := by
      have : g ∈ (K : Set (GL (Fin n) k)) := hK ▸ hg'
      exact this
    have hinv : g⁻¹ ∈ ball n r := by
      have : g⁻¹ ∈ (K : Set (GL (Fin n) k)) := K.inv_mem hgK
      exact hK ▸ this
    exact hVU g (hr hg') (hr hinv)
  · intro W hW
    obtain ⟨r, h0, h1, hr⟩ := pi_rad (X := fun _ : Fin n => kˣ) (1 : Fin n → kˣ)
      (fun _ r => {u : kˣ | valuation k ((u : k) - 1) ≤ r}) (fun i Y hY => by
        obtain ⟨V, hV, hVU⟩ := unit_nhds hY
        obtain ⟨r, h0, h1, hr⟩ := nhds_rad hV
        exact ⟨r, h0, h1, fun u hu => hVU u (hr hu) (hr (near_inv' h1 u hu))⟩)
      (fun _ r r' h y hy => (show valuation k ((y : k) - 1) ≤ r from le_trans hy h)) hW
    exact ⟨r, h0, h1, fun r' hr' u hu => hr fun i => (hu i).trans hr'⟩
  · intro r h1
    refine ⟨{ carrier := {u | Near r u}
              one_mem' := fun i => by simp
              mul_mem' := fun {a b} ha hb i => by
                simpa using near_mul' h1 (ha i) (hb i)
              inv_mem' := fun {a} ha i => by
                simpa using near_inv' h1 (a i) (ha i) }, fun u => Iff.rfl, ?_⟩
    have h := isCompact_univ_pi (fun _ : Fin n => compact_units r h1)
    convert h using 1
    ext u
    simp [Near, Set.mem_pi]
  · exact (continuous_leviEmb k (points (Fin n))).comp (continuous_leviTorus k (Fin n))
  · obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    refine ⟨fun i => Units.mk0 x hx0 ^ (n - (i : ℕ)), fun i j hij => ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    have hij' : (i : ℕ) < j := hij
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)) hx1 (by omega)
  · intro t₀ t h₀ ht i j hij
    have a := h₀ i j hij
    have b := ht i j hij
    have c : 0 < valuation k (t j : k) := zero_lt_iff.2 (by simp)
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    calc valuation k (t₀ i : k) * valuation k (t i : k) ≤ valuation k (t₀ i : k) * valuation k (t j : k) :=
          mul_le_mul_right b _
      _ < valuation k (t₀ j : k) * valuation k (t j : k) := mul_lt_mul_of_pos_right a c

end UpperTheory.Gal.InertialTypesAlt.L
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open scoped Classical ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

open PositivityTheory.Rg.Tf.Loc UpperTheory.V.Z.Tf.Orb

private theorem kSide (k : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)) (hμ : μk.IsHaarMeasure)
    (hk1 : μk (unitGL (n := Fin n) k : Set (GL (Fin n) k)) = 1)
    (U : Subgroup (GL (Fin n) k)) (f : GL (Fin n) k → ℂ)
    (hL : GlobalTheory.BCT.IsLevel (MonoidHom.id _) (unitGL k) U) (hH : GlobalTheory.BCT.IsHecke U f)
    (γ : GL (Fin n) k) (hγ : IsRegSemisimple γ) (μγ : Measure (Subgroup.centralizer {γ}))
    (hh : μγ.IsHaarMeasure) :
    IsCompact (GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ}) : Set (GL (Fin n) k)) ∧
    ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) ≠ 0) ∧
    orbIntegralC μk γ μγ f =
      ((μγ.real {t : Subgroup.centralizer {γ} |
        (t : GL (Fin n) k) ∈ GlobalTheory.BCT.cptPart (Subgroup.centralizer {γ})} : ℝ) : ℂ)⁻¹ *
        GlobalTheory.BCT.twOrb (MonoidHom.id _) (unitGL k) γ f := by
  obtain ⟨hLC, hSC, hT2, -, -⟩ := gLTop_holds k n
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds k n
  haveI : ValuativeExtension k k := ⟨by simp⟩
  obtain ⟨hgen, hσ1, hTw, -⟩ := untwist_holds k n μk γ
  have hT : Subgroup.centralizer {γ} = GlobalTheory.BCT.twCent (MonoidHom.id (GL (Fin n) k)) γ := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Iff.rfl
  have hTcl : IsClosed (Subgroup.centralizer {γ} : Set (GL (Fin n) k)) := by
    rw [hT]
    show IsClosed {g : GL (Fin n) k | g * γ = γ * (MonoidHom.id (GL (Fin n) k)) g}
    exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hcommA : ∀ t ∈ Subgroup.centralizer {γ}, Commute t γ :=
    fun t ht => Subgroup.mem_centralizer_singleton_iff.1 ht
  have hcomm : ∀ a ∈ Subgroup.centralizer {γ}, ∀ b ∈ Subgroup.centralizer {γ}, Commute a b := by
    intro a ha b hb
    have hm : ∀ t ∈ Subgroup.centralizer {γ},
        Commute (t : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
      intro t ht
      have h := Subgroup.mem_centralizer_singleton_iff.1 ht
      show (t : Matrix (Fin n) (Fin n) k) * γ = γ * t
      rw [← Units.val_mul, ← Units.val_mul, h]
    have h := centComm_holds k n (γ : Matrix (Fin n) (Fin n) k) a b hγ (hm a ha) (hm b hb)
    show a * b = b * a
    exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h.eq)
  have hC := cptCpt k n γ _ hγ hTcl hcommA
  have hcm : CptMod (Subgroup.centralizer {γ})
      (fun x => f (x⁻¹ * γ * (MonoidHom.id (GL (Fin n) k)) x)) := by
    obtain ⟨D, hD, hDp⟩ := orbProper_holds k k 1 hgen n γ (hTw hγ) (tsupport f) hH.1
    refine ⟨D, hD, fun g hg => ?_⟩
    have hg' : twConj (sigmaGL (1 : Gal(k/k))) g γ ∈ tsupport f := by
      have he : twConj (sigmaGL (1 : Gal(k/k))) g γ = g⁻¹ * γ * g := by
        show g⁻¹ * γ * (sigmaGL (1 : Gal(k/k))) g = g⁻¹ * γ * g
        rw [hσ1 g]
      rw [he]
      exact subset_tsupport f hg
    obtain ⟨t, ht, d, hd, rfl⟩ := hDp g hg'
    refine ⟨t, ?_, d, hd, rfl⟩
    have h1 := (mem_twCent _ _ _).1 ht
    rw [hσ1 t] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * γ = t * (t⁻¹ * γ * t) := by rw [h1]
      _ = γ * t := by group
  obtain ⟨hne, heq⟩ := orbSum (GL (Fin n) k) μk hμ (unitGL k) hKo hKc hk1 (MonoidHom.id _)
    continuous_id γ (Subgroup.centralizer {γ}) hT hcomm hC μγ hh U f hL hH hcm
  exact ⟨hC, hne, heq⟩

theorem matchOfSum : MatchOfSum := by
  unfold MatchOfSum
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ _ _ μE μk hμE hμk hE1 hk1 UE Uk φ f hLE hLk hHE hHk
    hmatch hsurj
  obtain ⟨hgal, hnorm, htw, -, hpair, hnormOf⟩ := dict k E σ hgen n
  obtain ⟨hLCE, hSCE, hT2E, -, -⟩ := gLTop_holds E n
  haveI := hLCE
  haveI := hSCE
  haveI := hT2E
  obtain ⟨hLCk, hSCk, hT2k, -, -⟩ := gLTop_holds k n
  haveI := hLCk
  haveI := hSCk
  haveI := hT2k
  obtain ⟨hKo, hKc, -⟩ := unitSB_holds E n
  obtain ⟨-, -, hcontE⟩ := extCont_holds k E
  have hgalg : ∀ g : GL (Fin n) E, (GlobalTheory.LBC.galAct σ n) g = (sigmaGL σ) g :=
    fun g => DFunLike.congr_fun hgal g
  have hθc : Continuous (GlobalTheory.LBC.galAct σ n) := by
    have h := (hcontE n).2 σ
    have he : (⇑(GlobalTheory.LBC.galAct σ n)) = ⇑(sigmaGL (n := Fin n) σ) := funext hgalg
    rw [he]
    exact h
  have hpow : (sigmaGL (n := Fin n) σ) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one', sigmaGL_one]
  refine ⟨?_, ?_⟩
  · intro δ γ h μδ μγ hTw hnh hδ hγh hmap
    obtain ⟨hγ, hchar, hmem⟩ := hpair δ h γ hTw hnh
    obtain ⟨hCk, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    obtain ⟨hTcl, hcomm⟩ := twCent_holds k E σ hgen n δ hTw
    have hT : PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ = GlobalTheory.BCT.twCent (GlobalTheory.LBC.galAct σ n) δ := by
      rw [hgal]
      exact htw δ
    have hCE : IsCompact (GlobalTheory.BCT.cptPart (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) : Set (GL (Fin n) E)) :=
      cptCpt E n (normGL σ δ) _ hTw hTcl (fun t ht => twCent_commute_twNorm (sigmaGL σ) hpow δ ht)
    have hcm : CptMod (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ)
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      obtain ⟨D, hD, hDp⟩ := orbProper_holds k E σ hgen n δ hTw (tsupport φ) hHE.1
      refine ⟨D, hD, fun g hg => ?_⟩
      have hg2 : φ (g⁻¹ * δ * (sigmaGL σ) g) ≠ 0 := by
        rw [← hgalg]
        exact hg
      exact hDp g (subset_tsupport φ hg2)
    obtain ⟨-, heqE⟩ := orbSum (GL (Fin n) E) μE hμE (unitGL E) hKo hKc hE1 (GlobalTheory.LBC.galAct σ n) hθc δ _
      hT hcomm hCE μδ hδ UE φ hLE hHE hcm
    have hvol := cptConj (GL (Fin n) E) (GL (Fin n) k) incl (inclClosed_holds k E n)
      (PositivityTheory.Rg.Tf.Loc.twCent (sigmaGL σ) δ) (Subgroup.centralizer {γ}) h hmem hCk μδ μγ hmap
    have hO : GlobalTheory.BCT.twOrb (GlobalTheory.LBC.galAct σ n) (unitGL E) δ φ =
        GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f :=
      hmatch δ (by rw [hnorm]; exact hTw) γ (by rw [hnorm]; exact hchar)
    have hL : twOrbIntegralC (sigmaGL σ) μE δ μδ φ = quotIntegral μE _ μδ
        (fun x => φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)) := by
      refine congrArg (quotIntegral μE _ μδ) (funext fun x => ?_)
      show φ (x⁻¹ * δ * (sigmaGL σ) x) = φ (x⁻¹ * δ * (GlobalTheory.LBC.galAct σ n) x)
      rw [hgalg]
    rw [heqk, hL, heqE, hO, hvol]
  · intro γ μγ hγ hno hγh
    obtain ⟨-, -, heqk⟩ := kSide k n μk hμk hk1 Uk f hLk hHk γ hγ μγ hγh
    rw [heqk]
    have h0 : GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (unitGL k) γ f = 0 := by
      by_contra hne
      obtain ⟨δ, hδ⟩ := hsurj γ hγ hne
      exact hno ⟨δ, hnormOf δ γ hγ (by rw [← hnorm]; exact hδ)⟩
    rw [h0, mul_zero]

end UpperTheory.Gal.InertialTypesAlt.L
end
