module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle064
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.FibPow

theorem smoothOfRelativeDimension_pow {X : Scheme.{0}} (A : Over X) (g : ℕ)
    (hA : SmoothOfRelativeDimension g A.hom) (k : ℕ) : SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  let e : GlobalTheory.KS.pow A k ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A k :=
    (limit.isLimit (Discrete.functor fun _ : Fin k => A)).conePointUniqueUpToIso
      (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A k)
  have hw : (GlobalTheory.KS.pow A k).hom = e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom := (Over.w e.hom).symm
  have h1 := GlobalTheory.smoothOfRelativeDimension_powObj A g hA k
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + k * g) (e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom) :=
    inferInstance
  rw [hw]; simpa using h2

theorem smoothOfRelativeDimension_fibrePower : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d g : ℕ),
    SmoothOfRelativeDimension d s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ k : ℕ, SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ X s d g hs A _ _ _ hA k
  have h := smoothOfRelativeDimension_pow A g hA k
  have h2 : SmoothOfRelativeDimension (k * g + d) ((GlobalTheory.KS.pow A k).hom ≫ s) := inferInstance
  rw [Nat.add_comm]; exact h2

end GlobalTheory.FibPow
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

theorem _root_.GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U : Type) [AddCommGroup U] [Module ℂ U] (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) k) U) (A : Representation ℂ (GL (Fin r) k) V) (B : Representation ℂ (GL (Fin t) k) W), π.IsIrreducible → IsSmooth A → IsSmooth B → HasFiniteLength A → HasFiniteLength B → IsSubquotient π (prod₂ A B) → ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π A ∧ IsSubquotient σ₂.π B ∧ IsSubquotient π (prod₂ σ₁.π σ₂.π) := by
  first | exact @GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ | exact GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ | (intros; apply GlobalTheory.ParIndExact.exists_irr_isSubquotient_prod₂ <;> assumption)
end

section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_add_etaHat_add_sHat_le_hPage {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  have ht : 5 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hS : 0 < L.Sc := L.Sc_pos
  obtain ⟨hC, hw1, hw2, hwb, -, hb⟩ := h
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hb' : (100 : ℝ) ≤ L.sc.b' := hw1.trans hwb
  have hfac : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbig : 100 * L.sc.b' ≤ L.sc.b := by
    have := mul_le_mul_of_nonneg_right hfac (by linarith : (0 : ℝ) ≤ L.sc.b')
    linarith
  have htR : ((D.R.t : ℕ) : ℝ) ≤ L.sc.b := by nlinarith
  have hb0 : 0 ≤ L.sc.b := by linarith
  set c := (D.R.t + 1) / 2 with hcdef
  have hc3 : 3 ≤ c := by omega
  have hct : c ≤ D.R.t := by omega
  have htc : D.R.t ≤ ⌈L.sc.b⌉₊ := by exact_mod_cast htR.trans (Nat.le_ceil _)
  have hcle : c ≤ ⌈L.sc.b⌉₊ := hct.trans htc
  have h1 : (⌈L.sc.b⌉₊ : ℝ) < L.sc.b + 1 := Nat.ceil_lt_add_one hb0
  have h2 : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le hη.le
  have h3 : (⌊L.Sc⌋₊ : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have hc3R : (3 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc3
  unfold bHat etaHat sHat hPage
  rw [← hcdef, Nat.cast_sub hcle]
  push_cast
  linarith

end GlobalTheory.HTW
end

section

noncomputable section

namespace GlobalTheory.BlockType

open GlobalTheory.SplitWeil ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_one_of_mem_KO {n : Type} [Fintype n] [DecidableEq n] {h : GL n k} (hh : h ∈ KO k n) (a b : n) :
    valuation k (h.val a b) ≤ 1 := by
  obtain ⟨g, rfl⟩ := hh
  exact (g.val a b).2

theorem val_col_lt {n : Type} [Fintype n] [DecidableEq n] {h g : GL n k} (hh : h ∈ KO k n) (b : n)
    (hg : ∀ c, valuation k ((g.val - 1) c b) < 1) (a : n) : valuation k ((h.val * (g.val - 1)) a b) < 1 := by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_lt _ one_ne_zero fun c _ => by
    rw [map_mul]; exact Right.mul_lt_one_of_le_of_lt (val_le_one_of_mem_KO hh a c) (hg c)


variable (k) in
def blockGrp (r t : ℕ) : Subgroup (GL (Fin (r + t)) k) where
  carrier := {h | h ∈ KO k (Fin (r + t)) ∧
    ∀ (a : Fin (r + t)) (j : Fin r), valuation k ((h.val - 1) a (Fin.castAdd t j)) < 1}
  one_mem' := ⟨(KO k _).one_mem, fun a j => by simp⟩
  mul_mem' := by
    rintro h g ⟨hh, h1⟩ ⟨hg, g1⟩
    refine ⟨(KO k _).mul_mem hh hg, fun a j => ?_⟩
    have e : ((h * g).val - 1) = h.val * (g.val - 1) + (h.val - 1) := by
      simp only [Units.val_mul, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, Matrix.add_apply]
    exact Valuation.map_add_lt _ (val_col_lt hh _ (fun c => g1 c j) a) (h1 a j)
  inv_mem' := by
    rintro h ⟨hh, h1⟩
    refine ⟨(KO k _).inv_mem hh, fun a j => ?_⟩
    have e : ((h⁻¹ : GL (Fin (r + t)) k).val - 1) = -((h⁻¹ : GL (Fin (r + t)) k).val * (h.val - 1)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]; abel
    rw [e, Matrix.neg_apply, Valuation.map_neg]
    exact val_col_lt ((KO k _).inv_mem hh) _ (fun c => h1 c j) a


open Classical in
def blockChar {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) : ℂ :=
  if hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det = 0 then 0 else (χ (Units.mk0 _ hd) : ℂ)

theorem blockChar_eq {r t : ℕ} (χ : kˣ →* ℂˣ) (h : GL (Fin (r + t)) k) (u : kˣ)
    (hu : (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det) : blockChar χ h = χ u := by
  have hd : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := hu ▸ u.ne_zero
  rw [blockChar, dite_eq_right hd]
  congr 2
  ext; simp [hu]

theorem mem_blockGrp {r t : ℕ} {h : GL (Fin (r + t)) k} (hK : h ∈ KO k (Fin (r + t)))
    (h1 : ∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1)
    (h2 : ∀ i j : Fin r, valuation k (h.val (Fin.castAdd t i) (Fin.castAdd t j) - if i = j then 1 else 0) < 1) :
    h ∈ blockGrp k r t := by
  refine ⟨hK, fun a j => ?_⟩
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · have := h2 i j
    simpa [Matrix.sub_apply, Matrix.one_apply, Fin.castAdd_inj] using this
  · have := h1 i j
    have hne : Fin.natAdd r i ≠ Fin.castAdd t j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simpa [Matrix.sub_apply, Matrix.one_apply, hne] using this

theorem isBlockVec_of {r t : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (χ : kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W)
    (hv : ∀ h ∈ blockGrp k r t, π h v = blockChar χ h • v) : GlobalTheory.SplitRead.IsBlockVec χ π v := by
  intro h hK h1 h2 u hu
  rw [hv h (mem_blockGrp hK h1 h2), blockChar_eq χ h u hu]

theorem kOne_le_blockGrp (r t : ℕ) : KOne k (Fin (r + t)) ≤ blockGrp k r t := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨⟨g, rfl⟩, fun a j => ?_⟩
  have hg' : ∀ a b, IsLocalRing.residue 𝒪[k] (g.val a b) = (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k]) a b := by
    intro a b
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val a b) hg
    simpa using this
  have hm : g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hg']
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e]
  have := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val - 1) a (Fin.castAdd t j) =
      ((g.val a (Fin.castAdd t j) - (1 : Matrix (Fin (r + t)) (Fin (r + t)) 𝒪[k]) a (Fin.castAdd t j) : 𝒪[k]) : k) := by
    by_cases e : a = Fin.castAdd t j <;> simp [Matrix.one_apply, e] <;> rfl
  rw [e]; exact this

theorem blockChar_kOne {r t : ℕ} (χ : kˣ →* ℂˣ) (hχ : IsTame χ) {h : GL (Fin (r + t)) k}
    (hh : h ∈ KOne k (Fin (r + t))) : blockChar χ h = 1 := by
  obtain ⟨g, hg, rfl⟩ := hh
  have hg' : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (IsLocalRing.residue 𝒪[k]) = 1 := by
    have := congrArg (fun x : GL (Fin (r + t)) 𝓀[k] => x.val) hg
    ext a b
    have h2 := congrArg (fun M : Matrix (Fin (r + t)) (Fin (r + t)) 𝓀[k] => M (Fin.natAdd r a) (Fin.natAdd r b)) this
    simpa [Matrix.one_apply, Fin.natAdd_inj] using h2
  have hm : (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 ∈ 𝓂[k] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, RingHom.map_det, RingHom.mapMatrix_apply, hg', Matrix.det_one, map_one, sub_self]
  have hv := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp ((IsLocalRing.mem_maximalIdeal _).1 hm)
  have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det =
      (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) := by
    rw [show ((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : k) =
      algebraMap 𝒪[k] k (g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det from rfl, RingHom.map_det]
    rfl
  have hne : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det : 𝒪[k]) : k) ≠ 0 := by
    intro h0
    have : (((g.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1 : 𝒪[k]) : k) = -1 := by
      push_cast; rw [h0]; ring
    rw [this, Valuation.map_neg, map_one] at hv
    exact lt_irrefl _ hv
  rw [blockChar_eq χ _ (Units.mk0 _ hne) e.symm, hχ (Units.mk0 _ hne) (by simpa using hv)]
  simp

end GlobalTheory.BlockType
end
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem block_map_reflect (R : Ranks) :
    (block R).map (fun u => (R.t : ℤ) - 1 - u) = block R := by
  have hnd : (block R).Nodup := by
    unfold block
    exact (Multiset.nodup_range R.t).map (fun a b h => by exact_mod_cast h)
  have hmem : ∀ x : ℤ, x ∈ block R ↔ 0 ≤ x ∧ x < R.t := by
    intro x
    unfold block
    simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by positivity, by exact_mod_cast hc⟩
    · rintro ⟨h0, h1⟩
      exact ⟨x.toNat, by omega, by omega⟩
  refine (Multiset.Nodup.ext (hnd.map (fun a b h => by simpa using h)) hnd).2 ?_
  · intro x
    rw [Multiset.mem_map, hmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hmem] at hy
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨(R.t : ℤ) - 1 - x, by rw [hmem]; omega, by ring⟩

theorem jR_symm_card {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧
      (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hW : ∀ s, (jW P j s).card = R.r := by
    intro s
    have h : (cloud P j + lows P j).card = R.r := by
      simp only [Multiset.card_add, cloud, lows, Multiset.card_map, Finset.card_val,
        Finset.card_univ, Fintype.card_fin, Ranks.r]
      omega
    cases s
    · simp only [jW, Bool.false_eq_true, if_false, Multiset.card_map, h]
    · simp only [jW, if_true, h]
  refine ⟨?_, fun s => ?_⟩
  · simp only [jR, jW, if_true, Bool.false_eq_true, if_false, Multiset.map_add (f := _), block_map_reflect]
  · have hR : (jR P j s).card = R.nV := by
      simp only [jR, Multiset.card_add, hW s, block, Multiset.card_map, Multiset.card_range, Ranks.nV]
    refine ⟨hW s, hR, ?_, ?_⟩
    · simp only [jT2, Multiset.card_map, hW s]
    · unfold jT2 jT1 jR
      exact Multiset.map_le_map (Multiset.le_add_right _ _)

end GlobalTheory.HTW
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem jT1_mem_window_of_bounded_v : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ),
    (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) →
    (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s,
    (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ)
      else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨
    |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  intro R P j s S η hv hb u hu
  obtain ⟨c, hc⟩ := R.t_odd
  have ht1 : ((R.t : ℤ) - 1) / 2 = c := by rw [hc]; push_cast; omega
  have ht2 : ((R.t : ℤ) + 1) / 2 = c + 1 := by rw [hc]; push_cast; omega
  have htc : (R.t : ℤ) = 2 * c + 1 := by rw [hc]; push_cast; ring
  obtain ⟨E, hE⟩ := P.e_int j
  have hEf : ⌊P.e j⌋ = E := by rw [hE]; simp
  have hV : ∀ i, 0 ≤ ⌊P.v i⌋ ∧ ⌊P.v i⌋ ≤ ((⌊S⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨V, hVi⟩ := P.v_int i
    obtain ⟨h0, h1⟩ := hv i
    rw [hVi] at h0 h1 ⊢
    simp only [Int.floor_intCast]
    push_cast at h0 h1
    have h0' : (0:ℤ) ≤ V := by exact_mod_cast h0
    refine ⟨h0', ?_⟩
    have h2 : ((V.toNat : ℕ) : ℝ) ≤ S := by
      have : ((V.toNat : ℕ) : ℝ) = (V : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0'
      rw [this]; exact h1
    have := Nat.le_floor h2
    omega
  have hB : ∀ i, -((⌊η⌋₊ : ℕ) : ℤ) ≤ ⌊P.b i⌋ - E ∧ ⌊P.b i⌋ - E ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by
    intro i
    obtain ⟨B, hBi⟩ := P.b_int i
    have h1 := hb i
    rw [hBi, hE] at h1
    rw [hBi]
    simp only [Int.floor_intCast]
    have h2 : (((B - E).natAbs : ℕ) : ℝ) ≤ η := by
      rw [Nat.cast_natAbs]; push_cast at h1 ⊢; exact h1
    have h3 := Nat.le_floor h2
    have h4 : |B - E| ≤ ((⌊η⌋₊ : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h3
    exact abs_le.mp h4
  simp only [jT1, jR, jW, cloud, lows, block, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
    Finset.mem_univ, true_and, Multiset.mem_range] at hu
  cases s with
  | true =>
    simp only [szT, if_true, Bool.not_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [if_true, Multiset.mem_map, Multiset.mem_add, Finset.mem_val, Finset.mem_univ,
      true_and] at hu
    obtain ⟨x, (hx | hx) | hx, rfl⟩ := hu
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hV i
      left; rw [hEf, ht1]; constructor <;> omega
    · obtain ⟨i, rfl⟩ := hx
      obtain ⟨a, b⟩ := hB i
      right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega
  | false =>
    simp only [szT, Bool.not_false, if_true, Bool.false_eq_true, if_false, ht2, hEf]
    simp only [Bool.false_eq_true, if_false, Multiset.mem_map, Multiset.mem_add, Finset.mem_val,
      Finset.mem_univ, true_and] at hu
    obtain ⟨x, hx | hx, rfl⟩ := hu
    · obtain ⟨y, hy | hy, rfl⟩ := hx
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hV i
        left; rw [hEf, ht1]; constructor <;> omega
      · obtain ⟨i, rfl⟩ := hy
        obtain ⟨a, b⟩ := hB i
        right; rw [abs_le, hEf, ht1]; push_cast; constructor <;> omega
    · obtain ⟨a, ha, rfl⟩ := hx
      right; rw [abs_le]; push_cast; constructor <;> omega

end GlobalTheory
end

section

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_S_eta_m : ∀ {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), ((pageWord L j ε τ φ).S : ℝ) ≤ L.Sc ∧ ((pageWord L j ε τ φ).η : ℝ) ≤ L.etaSz + D.R.t + 2 ∧ (pageWord L j ε τ φ).m = D.R.m := by
  intro D L j ε τ φ
  refine ⟨?_, ?_, rfl⟩
  · exact Nat.floor_le L.Sc_pos.le
  · have h := Nat.floor_le L.etaSz_pos.le
    show ((⌊L.etaSz⌋₊ + D.R.t + 2 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

end GlobalTheory.HTW
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.satakeParameters_bounded_lattice_eigenfunction : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : Lat O K r → E) (α : Multiset ℂ) (C : ℝ), α.card = r → φ ≠ 0 → (∀ L, ‖φ L‖ ≤ C) → (∀ k ≤ r, ∀ L, heckeElem k φ L = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • φ L) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.SatakeBound.main | exact GlobalTheory.SatakeBound.main | (intros; apply GlobalTheory.SatakeBound.main <;> assumption)
end
