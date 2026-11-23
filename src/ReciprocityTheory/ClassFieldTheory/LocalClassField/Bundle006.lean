module

public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle003
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle004
public import Lemmata.FirstBlockLemmaC.Imports
public import Lemmata.FirstBlockLemmaD.Imports
public import Lemmata.PadicNatCastNorm.NormNatCastOfNotDvd
public import ReciprocityTheory.GroupCohomology.Bundle002
public import ReciprocityTheory.NeutralLocalFields.Duality
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GroupCohomology.ComapZeroCoboundariesEqBot

@[expose] public section

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 Function

noncomputable section

theorem qz_mk_eq_zero_iff (q : ℚ) : (QuotientAddGroup.mk q : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]; rfl

theorem qz_nsmul_mk (l : ℕ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← nsmul_eq_mul]; rfl

theorem qz_zsmul_mk (l : ℤ) (q : ℚ) : l • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((l : ℚ) * q) := by
  rw [← zsmul_eq_mul]; rfl

theorem qz_exists_zsmul (n : ℕ) (hn : n ≠ 0) (x : QZ) (hx : n • x = 0) :
    ∃ k : ℤ, x = k • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff] at hx
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  rw [qz_zsmul_mk, hk]
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  congr 1
  field_simp

theorem qz_nsmul_inv_eq_zero_iff (n : ℕ) (hn : n ≠ 0) (l : ℕ) :
    l • (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) = 0 ↔ n ∣ l := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [qz_nsmul_mk, qz_mk_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    have h : ((k * n : ℤ) : ℚ) = ((l : ℤ) : ℚ) := by
      push_cast
      rw [hk]
      field_simp
    have h' : k * n = (l : ℤ) := Int.cast_injective h
    exact Int.natCast_dvd_natCast.1 ⟨k, by rw [← h', mul_comm]⟩
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    push_cast
    field_simp

scoped instance hasEnoughRootsOfUnity_QZ (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (Multiplicative QZ) n where
  prim := ⟨Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n)),
    { pow_eq_one := by
        rw [← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]; rfl
      dvd_of_pow_eq_one := fun l hl => by
        rw [← ofAdd_nsmul] at hl
        exact (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) l).1 (Multiplicative.ofAdd.injective hl) }⟩
  cyc := by
    have h0 : (toUnits (Multiplicative.ofAdd (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ))) ∈
        rootsOfUnity n (Multiplicative QZ) := by
      rw [mem_rootsOfUnity, ← map_pow, ← ofAdd_nsmul, (qz_nsmul_inv_eq_zero_iff n (NeZero.ne n) n).2 dvd_rfl]
      exact map_one _
    refine ⟨⟨⟨_, h0⟩, fun x => ?_⟩⟩
    have hx : n • Multiplicative.toAdd (x.1 : Multiplicative QZ) = 0 := by
      have := x.2
      rw [mem_rootsOfUnity] at this
      have h2 := congrArg (fun u : (Multiplicative QZ)ˣ => Multiplicative.toAdd (u : Multiplicative QZ)) this
      simpa using h2
    obtain ⟨k, hk⟩ := qz_exists_zsmul n (NeZero.ne n) _ hx
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Units.ext
    apply Multiplicative.toAdd.injective
    rw [hk]
    simp

section fin

variable (A : Type) [AddCommGroup A] [Finite A]

def homEquivUnits : (A →+ QZ) ≃ (Multiplicative A →* (Multiplicative QZ)ˣ) :=
  AddMonoidHom.toMultiplicative.trans (toUnits (G := Multiplicative QZ)).monoidHomCongrRight.toEquiv

theorem homEquivUnits_apply (χ : A →+ QZ) (a : A) :
    Multiplicative.toAdd ((homEquivUnits A χ (Multiplicative.ofAdd a) : (Multiplicative QZ)ˣ) : Multiplicative QZ) = χ a := rfl

scoped instance : NeZero (Monoid.exponent (Multiplicative A)) := ⟨Monoid.exponent_ne_zero_of_finite⟩

theorem card_hom_QZ : Nat.card (A →+ QZ) = Nat.card A := by
  rw [Nat.card_congr (homEquivUnits A),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)]
  rfl

scoped instance finite_hom_QZ : Finite (A →+ QZ) :=
  Nat.finite_of_card_ne_zero (by rw [card_hom_QZ]; exact Nat.card_pos.ne')

variable {A}

theorem exists_hom_QZ_ne_zero {a : A} (ha : a ≠ 0) : ∃ χ : A →+ QZ, χ a ≠ 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative A) (Multiplicative QZ)
    (a := Multiplicative.ofAdd a) (fun h => ha (Multiplicative.ofAdd.injective h))
  refine ⟨(homEquivUnits A).symm φ, fun h => hφ ?_⟩
  rw [← homEquivUnits_apply, Equiv.apply_symm_apply] at h
  exact Units.ext (Multiplicative.toAdd.injective h)

theorem exists_eval_QZ (f : (A →+ QZ) →+ QZ) : ∃ a : A, ∀ χ : A →+ QZ, χ a = f χ := by
  let ev : A →+ ((A →+ QZ) →+ QZ) := AddMonoidHom.flip (AddMonoidHom.id (A →+ QZ))
  have hinj : Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h
    obtain ⟨χ, hχ⟩ := exists_hom_QZ_ne_zero h
    exact hχ (DFunLike.congr_fun ha χ)
  have hbij : Bijective ev := hinj.bijective_of_nat_card_le (by rw [card_hom_QZ, card_hom_QZ])
  obtain ⟨a, ha⟩ := hbij.2 f
  exact ⟨a, fun χ => DFunLike.congr_fun ha χ⟩

end fin

section top

variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))

def pullChar : (A →+ QZ) →+ charGrp G where
  toFun ψ := ⟨ψ.comp π, hc.comp ψ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pullChar_apply (ψ : A →+ QZ) (g : G) : (pullChar π hc ψ).1 (Additive.ofMul g) = ψ (π (Additive.ofMul g)) := rfl

variable {π}

theorem pullChar_injective (hπ : Surjective π) : Injective (pullChar π hc) := by
  intro ψ ψ' h
  ext a
  obtain ⟨g, rfl⟩ := hπ a
  exact DFunLike.congr_fun (congrArg Subtype.val h) g

theorem exists_pullChar_eq (hπ : Surjective π) (χ : charGrp G)
    (h : ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) : ∃ ψ, pullChar π hc ψ = χ := by
  refine ⟨π.liftOfSurjective hπ ⟨χ.1, fun g hg => h (Additive.toMul g) hg⟩, Subtype.ext ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ _

include hc

theorem exists_character_ne_zero_of_quotient [Finite A] (g : G) (hg : π (Additive.ofMul g) ≠ 0) :
    ∃ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) ∧ χ.1 (Additive.ofMul g) ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_QZ_ne_zero hg
  exact ⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero], hψ⟩

theorem card_characters_of_finite_quotient [Finite A] (hπ : Surjective π) :
    Nat.card {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0} = Nat.card A := by
  rw [← card_hom_QZ A]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun ψ : A →+ QZ => (⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero]⟩ :
      {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0})) ⟨?_, ?_⟩)).symm
  · intro ψ ψ' h
    exact pullChar_injective hc hπ (congrArg Subtype.val h)
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ⟩ := exists_pullChar_eq hc hπ χ hχ
    exact ⟨ψ, Subtype.ext hψ⟩

theorem exists_element_evaluating_characters [Finite A] (hπ : Surjective π) (f : charGrp G →+ QZ) :
    ∃ g : G, ∀ χ : charGrp G, (∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0) →
      χ.1 (Additive.ofMul g) = f χ := by
  obtain ⟨a, ha⟩ := exists_eval_QZ (f.comp (pullChar π hc))
  obtain ⟨g, rfl⟩ := hπ a
  refine ⟨Additive.toMul g, fun χ hχ => ?_⟩
  obtain ⟨ψ, rfl⟩ := exists_pullChar_eq hc hπ χ hχ
  exact ha ψ

end top

section quot

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal]

abbrev quotAddCommGroup (h : commutator G ≤ H) : AddCommGroup (Additive (G ⧸ H)) :=
  { (inferInstance : AddGroup (Additive (G ⧸ H))) with
    add_comm := fun a b => by
      have := (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).2 h
      exact congrArg Additive.ofMul (this.is_comm.comm (Additive.toMul a) (Additive.toMul b)) }

end quot

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField

variable {p : ℕ} [Fact p.Prime]

noncomputable abbrev res : Obar p →+* kbar p := IsLocalRing.residue (Obar p)

theorem norm_le_one (x : Obar p) : ‖(x : PadicAlgCl p)‖ ≤ 1 := mem_Obar_iff.1 x.2

theorem norm_sub_le_max' (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  first | exact Bl.FirstBlockLemmaD.goal1 .. | (apply Bl.FirstBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaD.goal1 <;> assumption)

theorem isUnit_iff (x : Obar p) : IsUnit x ↔ ‖(x : PadicAlgCl p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : Obar p) : PadicAlgCl p) * (((u⁻¹ : (Obar p)ˣ) : Obar p) : PadicAlgCl p) = 1 := by
      have h2 : (((u : Obar p) * ((u⁻¹ : (Obar p)ˣ) : Obar p) : Obar p) : PadicAlgCl p) = 1 := by
        rw [u.mul_inv]; rfl
      exact h2
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have ha := norm_le_one (u : Obar p)
    have hb := norm_le_one ((u⁻¹ : (Obar p)ˣ) : Obar p)
    have hb0 := norm_nonneg ((u : Obar p) : PadicAlgCl p)
    nlinarith
  · intro h
    have hx0 : (x : PadicAlgCl p) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hi : ‖(x : PadicAlgCl p)⁻¹‖ ≤ 1 := by rw [norm_inv, h, inv_one]
    refine IsUnit.of_mul_eq_one (⟨(x : PadicAlgCl p)⁻¹, mem_Obar_iff.2 hi⟩ : Obar p) ?_
    apply Subtype.ext
    exact mul_inv_cancel₀ hx0

theorem res_eq_zero_iff (x : Obar p) : res x = 0 ↔ ‖(x : PadicAlgCl p)‖ < 1 := by
  constructor
  · intro h
    by_contra hc
    have h1 : ‖(x : PadicAlgCl p)‖ = 1 := le_antisymm (norm_le_one x) (not_lt.1 hc)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit x).2 ((isUnit_iff x).2 h1) h
  · intro h
    by_contra hc
    have := (isUnit_iff x).1 ((IsLocalRing.residue_ne_zero_iff_isUnit x).1 hc)
    exact absurd this (ne_of_lt h)

theorem res_eq_iff (x y : Obar p) : res x = res y ↔ ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
  rfl

theorem mem_resK_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (c : kbar p) :
    c ∈ resK p K ↔ ∃ x : Obar p, (x : PadicAlgCl p) ∈ K ∧ res x = c := Iff.rfl

theorem resK_mono {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) : resK p K ≤ resK p L := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  exact (mem_resK_iff L _).2 ⟨x, h hx, rfl⟩

theorem norm_GK {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem norm_p_lt_one : ‖((p : ℕ) : PadicAlgCl p)‖ < 1 := by
  have h : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

scoped instance charP_kbar : CharP (kbar p) p := by
  obtain ⟨r, hr⟩ := CharP.exists (kbar p)
  have h0 : ((p : ℕ) : kbar p) = 0 := by
    have h1 : res ((p : ℕ) : Obar p) = 0 := by
      rw [res_eq_zero_iff]
      have : (((p : ℕ) : Obar p) : PadicAlgCl p) = ((p : ℕ) : PadicAlgCl p) := by simp
      rw [this]; exact norm_p_lt_one
    simpa using h1
  have h2 : r ∣ p := (CharP.cast_eq_zero_iff (kbar p) r p).1 h0
  have h3 : r = p := ((Nat.dvd_prime Fact.out).1 h2).resolve_left (CharP.char_ne_one (kbar p) r)
  exact h3 ▸ hr

theorem finite_resK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    Finite (resK p K) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hc : IsCompact (Metric.closedBall (0 : K) 1) := isCompact_closedBall 0 1
  obtain ⟨t, -, htf, hcov⟩ := finite_cover_balls_of_compact hc (e := 1) one_pos
  classical
  let g : K → kbar p := fun x => if h : ‖(x : PadicAlgCl p)‖ ≤ 1 then res ⟨x, mem_Obar_iff.2 h⟩ else 0
  have hsub : (resK p K : Set (kbar p)) ⊆ g '' t := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
    have hxb : (⟨x, hx⟩ : K) ∈ Metric.closedBall (0 : K) 1 := by
      rw [mem_closedBall_zero_iff]; exact norm_le_one x
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hxb)
    rw [Metric.mem_ball, dist_eq_norm] at hxy
    have hxy' : ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 := hxy
    have hy1 : ‖(y : PadicAlgCl p)‖ ≤ 1 := by
      have h1 : (y : PadicAlgCl p) = (x : PadicAlgCl p) - ((x : PadicAlgCl p) - (y : PadicAlgCl p)) := by ring
      rw [h1]
      exact (norm_sub_le_max' _ _).trans (max_le (norm_le_one x) hxy'.le)
    refine ⟨y, hy, ?_⟩
    have hg : g y = res ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩ := dif_pos hy1
    rw [hg]
    exact ((res_eq_iff x ⟨(y : PadicAlgCl p), mem_Obar_iff.2 hy1⟩).2 hxy').symm
  exact (htf.image g).subset hsub

theorem qK_eq_pow (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ f : ℕ, 0 < f ∧ qK p K = p ^ f := by
  have := finite_resK K hK
  have := Fintype.ofFinite (resK p K)
  have hch : CharP (resK p K) p :=
    ((resK p K).subtype.charP_iff Subtype.val_injective p).2 inferInstance
  obtain ⟨n, -, hn⟩ := FiniteField.card (resK p K) p
  exact ⟨n, n.pos, by rw [qK, Nat.card_eq_fintype_card, hn]⟩

theorem one_lt_qK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    1 < qK p K := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  rw [h]
  exact Nat.one_lt_pow hf.ne' (Fact.out : p.Prime).one_lt

theorem not_dvd_qK_pow_sub_one (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    {n : ℕ} (hn : 0 < n) : ¬ p ∣ qK p K ^ n - 1 := by
  obtain ⟨f, hf, h⟩ := qK_eq_pow K hK
  intro hd
  have h1 : p ∣ qK p K ^ n := by
    rw [h, ← pow_mul]; exact dvd_pow_self p (Nat.mul_pos hf hn).ne'
  have h2 : 1 ≤ qK p K ^ n := Nat.one_le_pow _ _ (by have := one_lt_qK K hK; omega)
  have h3 : p ∣ 1 := by
    have := (Nat.dvd_sub h1 hd)
    rwa [Nat.sub_sub_self h2] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

theorem norm_eq_one_of_pow {m : ℕ} (hm : m ≠ 0) {ζ : PadicAlgCl p} (hζ : ζ ^ m = 1) : ‖ζ‖ = 1 := by
  first | exact Bl.FirstBlockLemmaC.goal1 .. | (apply Bl.FirstBlockLemmaC.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaC.goal1 <;> assumption)

theorem norm_sub_one_of_pow {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by
  first | exact Bl.PadicNatCastNorm.goal1 .. | (apply Bl.PadicNatCastNorm.goal1 <;> assumption) | (intros; apply Bl.PadicNatCastNorm.goal1 <;> assumption)

theorem norm_sub_eq_one_of_pow_eq_one {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0] at hξ; exact zero_ne_one hξ
  have h1 : ζ - ξ = ξ * (ζ / ξ - 1) := by field_simp
  rw [h1, norm_mul, norm_eq_one_of_pow hm0 hξ, one_mul]
  apply norm_sub_one_of_pow hm
  · rw [div_pow, hζ, hξ, div_one]
  · intro h2; exact h ((div_eq_one_iff_eq hξ0).1 h2)

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
end

section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem qz_mem_zmultiples {n : ℕ} (hn : 0 < n) (x : QZ) (hx : n • x = 0) :
    x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : (QuotientAddGroup.mk (n • q) : QZ) = 0 := hx
  obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
  have hk' : (k : ℚ) = n • q := hk
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  show (QuotientAddGroup.mk (k • ((1 : ℚ) / n)) : QZ) = _
  congr 1
  rw [zsmul_eq_mul, hk', nsmul_eq_mul]
  field_simp

section general

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G)

theorem exists_defect {t : G → ℚ} (χ : Additive G →+ QZ)
    (h : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g => by
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, h, h, h, ofMul_mul, map_add (f := _), sub_self]
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
    exact ⟨k, hk⟩
  choose m hm using this
  exact ⟨m, hm⟩

theorem isLocallyConstant_defect {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  refine IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) ?_ Int.cast_injective
  have : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [this]
  exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
    (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (x y w : G) :
    m ![y, w] - m ![x * y, w] + m ![x, y * w] = m ![x, y] := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem exists_defect_cocycle {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a) :
    ∃ z : M.coch.X 2, M.coch.d 2 z = 0 ∧ ∀ g, z.1 g = m g • a := by
  have hc : Continuous fun g => m g • a :=
    ((isLocallyConstant_defect ht hm).comp (fun k : ℤ => k • a)).continuous
  refine ⟨⟨fun g => m g • a, hc⟩, Subtype.ext (funext fun v => ?_), fun _ => rfl⟩
  show ReciprocityTheory.Gal.dn M.rho 2 (fun g => m g • a) v = 0
  rw [LowDeg.dn_two_apply, map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul,
    defect_cocycle hm, sub_self, zero_smul]

variable [Fintype G]

theorem sum_defect_smul {m : (Fin 2 → G) → ℤ} (a : M.V) (b : M.coch.X 1)
    (hb : ∀ g, (M.coch.d 1 b).1 g = m g • a) (τ : G) :
    (∑ σ, m ![σ, τ]) • a = ∑ σ, M.rho σ (b.1 ![τ]) := by
  have h1 : ∀ σ : G, m ![σ, τ] • a = M.rho σ (b.1 ![τ]) - b.1 ![σ * τ] + b.1 ![σ] := fun σ => by
    rw [← hb]
    exact LowDeg.dn_one_apply M.rho b.1 ![σ, τ]
  have h2 : ∑ σ, b.1 ![σ * τ] = ∑ σ, b.1 ![σ] := Equiv.sum_comp (Equiv.mulRight τ) (fun σ => b.1 ![σ])
  rw [Finset.sum_smul, Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  abel

theorem sum_defect {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (τ : G) :
    ((∑ σ, m ![σ, τ] : ℤ) : ℚ) = Fintype.card G * t τ := by
  push_cast
  rw [Finset.sum_congr rfl fun σ _ => hm ![σ, τ]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : ∑ σ, t (σ * τ) = ∑ σ, t σ := Equiv.sum_comp (Equiv.mulRight τ) t
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2]
  simp

theorem exists_cobound_of_norm [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (y : M.V) :
    ∃ b : M.coch.X 1, ∀ g, (M.coch.d 1 b).1 g = m g • ∑ ρ, M.rho ρ y := by
  refine ⟨⟨fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y, continuous_of_discreteTopology⟩, fun v => ?_⟩
  show ReciprocityTheory.Gal.dn M.rho 1 (fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y) v = _
  rw [LowDeg.dn_one_apply]
  simp only [Matrix.cons_val_zero]
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl

  rw [← Equiv.sum_comp (Equiv.mulLeft (v 1)) (fun ρ => m ![v 0, ρ] • M.rho (v 0 * ρ) y),
  ← Equiv.sum_comp (Equiv.mulLeft (v 0 * v 1)) (fun ρ => M.rho ρ y), map_sum, Finset.smul_sum,
  ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [map_zsmul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← sub_smul, ← add_smul, defect_cocycle hm, ← hv]

end general

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
end
