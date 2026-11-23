module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CompHS
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def headWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ (i : ℕ) ≤ k then 1 else 0


open Classical in
def tailWt (τ : Psi H) (k : ℕ) : AllWt.Weight Dw := fun τ' i => if τ' = τ ∧ k < (i : ℕ) then -1 else 0


open Classical in
def unitWt (τ : Psi H) (a : ℤ) : AllWt.Weight Dw := fun τ' _ => if τ' = τ then a else 0

theorem eq_last_add_gaps {N : ℕ} (v : Fin N → ℤ) (hN : 0 < N) (i : Fin N) :
    v i = v ⟨N - 1, by omega⟩ + ∑ k ∈ Finset.range (N - 1), if (i : ℕ) ≤ k then gap v k else 0 := by
  have h := ofGaps_gap v ⟨N - 1, by omega⟩ i
  simp only [ofGaps] at h
  have hi : (i : ℕ) ≤ N - 1 := by omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have e : (Finset.range (N - 1)).filter (fun k => (i : ℕ) ≤ k) = Finset.Ico (i : ℕ) (N - 1) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [e, Finset.sum_Ico_eq_sub _ hi]
  linarith


open Classical in
def piece (Dw : Datum H) (τ : Psi H) (k : ℕ) : AllWt.Weight Dw :=
  if k + 1 < Dw.p + Dw.q then (if k < Dw.p then headWt τ k else tailWt τ k) else 0

open Classical in
theorem piece_apply (τ τ' : Psi H) (k : ℕ) (i : Fin (Dw.p + Dw.q)) : piece Dw τ k τ' i =
    if τ' = τ then (if k + 1 < Dw.p + Dw.q then (if k < Dw.p then (if (i : ℕ) ≤ k then 1 else 0)
      else (if k < (i : ℕ) then -1 else 0)) else 0) else 0 := by
  unfold piece headWt tailWt
  by_cases h : τ' = τ <;> split_ifs <;> simp_all

open Classical in
theorem unitWt_apply (τ τ' : Psi H) (a : ℤ) (i : Fin (Dw.p + Dw.q)) :
    unitWt τ a τ' i = if τ' = τ then a else 0 := rfl

open Classical in
theorem decomp (la : AllWt.Weight Dw) (hla : GapGe 0 la) (hN : 0 < Dw.p + Dw.q) :
    let cτ : Psi H → ℤ := fun τ => la τ ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ) k else 0
    la = ∑ x ∈ (Finset.univ ×ˢ Finset.range (Dw.p + Dw.q - 1)).disjSum (Finset.univ : Finset (Psi H × Bool)),
      (Sum.elim (fun y : Psi H × ℕ => (gap (la y.1) y.2).toNat)
        (fun y : Psi H × Bool => if y.2 then (cτ y.1).toNat else (-cτ y.1).toNat) x) •
      (Sum.elim (fun y : Psi H × ℕ => piece Dw y.1 y.2)
        (fun y : Psi H × Bool => unitWt y.1 (if y.2 then 1 else -1)) x) := by
  intro cτ
  classical
  funext τ' i
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_disjSum, Finset.sum_product, Finset.univ_product_univ.symm,
    Finset.sum_product]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, piece_apply, unitWt_apply, Fintype.sum_bool,
    mul_ite, mul_zero, if_true, if_false]
  rw [Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp),
    Finset.sum_eq_single (s := Finset.univ) τ' (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp only [if_true, nsmul_eq_mul, Bool.false_eq_true, if_false, mul_one]
  have hv := eq_last_add_gaps (la τ') hN i
  have hterm : ∀ y ∈ Finset.range (Dw.p + Dw.q - 1), (if (i : ℕ) ≤ y then gap (la τ') y else 0) =
      ((gap (la τ') y).toNat : ℤ) * (if y + 1 < Dw.p + Dw.q then (if y < Dw.p then (if (i : ℕ) ≤ y then 1 else 0)
        else (if y < (i : ℕ) then -1 else 0)) else 0) + (if Dw.p ≤ y then gap (la τ') y else 0) := by
    intro y hy
    have hy' : y + 1 < Dw.p + Dw.q := by simp only [Finset.mem_range] at hy; omega
    have hg : 0 ≤ gap (la τ') y := hla τ' y hy'
    rw [Int.toNat_of_nonneg hg, if_pos hy']
    split_ifs <;> first | omega | simp <;> omega
  have hc := Int.toNat_sub_toNat_neg (cτ τ')
  have hcdef : cτ τ' = la τ' ⟨Dw.p + Dw.q - 1, by omega⟩ +
      ∑ k ∈ Finset.range (Dw.p + Dw.q - 1), if Dw.p ≤ k then gap (la τ') k else 0 := rfl
  rw [hv, Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  linarith

end GlobalTheory.NefWt
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem _root_.GlobalTheory.HSApp.exists_dominant_sub {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    (la ν : _root_.GlobalTheory.AllWt.Weight Dw) (hla : _root_.GlobalTheory.HSApp.GapGe (1 : ℤ) la) :
    ∃ mu : _root_.GlobalTheory.AllWt.Weight Dw, _root_.GlobalTheory.HSApp.GapGe (0 : ℤ) mu ∧
      ∃ m : ℕ, 0 < m ∧ m • la - mu = ν := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ τ : _root_.GlobalTheory.AllWt.Psi H, ∀ k : ℕ,
      k + 1 < Dw.p + Dw.q → _root_.GlobalTheory.CompHS.gap (ν τ) k ≤ M := by
    refine ⟨Finset.univ.sup fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat, fun τ k hk => ?_⟩
    have h := Finset.le_sup (f := fun p : _root_.GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q) =>
      (_root_.GlobalTheory.CompHS.gap (ν p.1) (p.2 : ℕ)).toNat)
      (Finset.mem_univ (τ, (⟨k, by omega⟩ : Fin (Dw.p + Dw.q))))
    exact (Int.self_le_toNat _).trans (by exact_mod_cast h)
  refine ⟨(M + 1) • la - ν, ?_, M + 1, Nat.succ_pos M, sub_sub_cancel _ _⟩
  unfold _root_.GlobalTheory.HSApp.GapGe at hla ⊢
  intro τ k hk
  have h₁ := hla τ k hk
  have h₂ := hM τ k hk
  unfold _root_.GlobalTheory.CompHS.gap at h₁ h₂ ⊢
  rw [dite_eq_left hk] at h₁ h₂ ⊢
  have e : ∀ i, ((M + 1) • la - ν) τ i = ((M + 1 : ℕ) : ℤ) * la τ i - ν τ i := by
    intro i
    simp
  rw [e, e]
  push_cast
  nlinarith

end GlobalTheory.HSApp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

section GapArith

variable {N : ℕ}

theorem gap_add (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]
    ring
  · simp

theorem gap_sub (v w : Fin N → ℤ) (k : ℕ) : gap (v - w) k = gap v k - gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.sub_apply]
    ring
  · simp

theorem gap_nsmul (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = n * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]
    ring
  · simp

end GapArith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem gap_kap (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) : gap (FlagTan.kap Dw τ) k =
    if k + 1 = Dw.p then 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 else -2 := by
  unfold FlagTan.kap gap
  simp only [dif_pos h]
  split_ifs <;> push_cast <;> omega

theorem gap_kap_le (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) :
    gap (FlagTan.kap Dw τ) k ≤ 2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2 := by
  rw [gap_kap τ h]
  split_ifs <;> omega

theorem div_le_sub_mul_div (g : ℤ) {n : ℤ} (hn : 0 < n) : g / n ≤ g - (n - 1) * (g / n) := by
  have h₁ : n * (g / n) ≤ g := by
    first
      | exact Int.mul_ediv_self_le hn.ne'
      | exact Int.mul_ediv_le hn g
      | (have := Int.emod_def g n; have := Int.emod_nonneg g hn.ne'; linarith)
      | (have := Int.ediv_mul_le g hn.ne'; linarith)
      | (have := Int.emod_add_mul_ediv g n; have := Int.emod_nonneg g hn.ne'; linarith)
  linarith

theorem gaps_of_wtBig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (P : WtPar Dw), WtBig P → ∀ la ∈ [P.u₁, P.u₂, P.ub, P.u₁ - FlagTan.kap Dw - (dimFlag Dw + 2) • P.ub], GapGe 1 la ∧ GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) := by
  intro E _ _ _ H Dw P hP la hla
  have hD3 : (0 : ℤ) < (dimFlag Dw : ℤ) + 3 := by positivity
  have hmain : ∀ (τ : Psi H) (k : ℕ), k + 1 < Dw.p + Dw.q →
      (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) + 4 * ((Dw.p : ℤ) + Dw.q) + dimFlag Dw + 3 ≤ gap (P.ub τ) k ∧
      gap (P.ub τ) k ≤ gap (P.u₁ τ) k - ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k ∧
      gap (P.u₁ τ) k ≤ gap (P.u₂ τ) k := by
    intro τ k h
    have hg := hP.gaps τ k h
    push_cast at hg
    rw [P.gap_ub τ h]
    refine ⟨?_, ?_, ?_⟩
    · apply Int.le_ediv_of_mul_le hD3
      linarith
    · have := div_le_sub_mul_div (gap (P.u₁ τ) k) hD3
      linarith
    · rw [show P.u₂ τ = P.u₁ τ + P.rem τ from rfl, gap_add]
      linarith [(P.gap_rem τ k).1]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hla
  rcases hla with rfl | rfl | rfl | rfl <;> constructor <;> intro τ k h <;>
  · obtain ⟨h₁, h₂, h₃⟩ := hmain τ k h
    have h₄ := gap_kap_le τ h
    push_cast at h₄
    have hC : (0 : ℤ) ≤ (((dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := by positivity
    have hD : (0 : ℤ) ≤ (dimFlag Dw : ℤ) := by positivity
    have hN : (2 : ℤ) ≤ (Dw.p : ℤ) + Dw.q := by omega
    have hb : (0 : ℤ) ≤ ((dimFlag Dw : ℤ) + 2) * gap (P.ub τ) k := by
      apply mul_nonneg <;> linarith
    try simp only [Pi.sub_apply, Pi.smul_apply, gap_sub, gap_nsmul]
    try push_cast
    linarith

end GlobalTheory.HSApp
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)

namespace GlobalTheory.OrbitSep

section Lin

variable {X : Scheme.{0}} [IsIntegral X] {Γ : Type} [Group Γ]

def fnAct (ρ : Γ →* Aut X) (γ : Γ) : X.functionFieldˣ →* X.functionFieldˣ :=
  haveI : IsIso (ρ γ).asIso.hom := Iso.isIso_hom (ρ γ).asIso
  Units.map (GlobalTheory.functionFieldMap (ρ γ).asIso.hom).toMonoidHom

def RatLin (ρ : Γ →* Aut X) (L : LB X) (hL : L.IsLB) : Prop :=
  ∃ (D : CartierDiv X) (c : Γ → X.functionFieldˣ), cls (toLB D) (isLB_toLB D) = cls L hL ∧
    (∀ γ δ, c (γ * δ) = fnAct ρ δ (c γ) * c δ) ∧
    (∀ γ x g, D.IsEqn ((ρ γ).asIso.hom x) g → D.IsEqn x (fnAct ρ γ g * (c γ)⁻¹)) ∧
    ∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).asIso.hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * (c γ)⁻¹ * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

section Base

variable (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

abbrev X₀ : Scheme.{0} := (barComp Y Z).toScheme

abbrev s₀ : X₀ Y Z ⟶ Sp c.F := (barComp Y Z).ι ≫ Y.s

abbrev V₀ : Scheme.{0} := (Y.j ⁻¹ᵁ barComp Y Z).toScheme

abbrev i₀ : V₀ Y Z ⟶ Xo.XF c := (Y.j ⁻¹ᵁ barComp Y Z).ι

abbrev j₀ : V₀ Y Z ⟶ X₀ Y Z := Y.j ∣_ barComp Y Z


variable {Y} in
abbrev π₀ (X : FlagCover Y) (Z : Comp Xo c) : Y₀ X Z ⟶ X₀ Y Z := X.π ∣_ barComp Y Z


variable {Y} in
theorem π₀_s₀ (X : FlagCover Y) (Z : Comp Xo c) : π₀ X Z ≫ s₀ Y Z = str₀ X Z := by
  dsimp only [π₀, s₀, str₀, inc₀, flagStr]
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc]

theorem j₀_ι : j₀ Y Z ≫ (barComp Y Z).ι = i₀ Y Z ≫ Y.j :=
  morphismRestrict_ι _ _


variable {Y Z} in
def ActsBy {Γ : Type} [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ Y Z)) : Prop :=
  (∀ γ, (ρ γ).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z) ∧
    ∀ (γ : Γ) (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R) (v : Sp R ⟶ V₀ Y Z), v ≫ i₀ Y Z = ptF y →
      v ≫ (ρ γ).asIso.hom ≫ i₀ Y Z = ptF (move Xo c (ι γ)⁻¹ y)

end Base


variable (Dw) in
def kapBase : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (Dw.q : ℤ) else -(Dw.p : ℤ)

def UnipAt (I : Ideal (𝓞 E)) (γ : LevelAut Dw l) : Prop :=
  ∃ m : ℕ, ∀ x : Dw.La, ((liftLa γ - 1) ^ m) x ∈ I • (⊤ : Submodule (𝓞 E) Dw.La)

def NeatPrime (I : Ideal (𝓞 E)) (g r : ℕ) : Prop :=
  g.Prime ∧ Ideal.absNorm I = g ∧ (g : 𝓞 E) ∉ I ^ 2 ∧ r + 1 < g

theorem gapGe_sub_kapBase (t : ℤ) (ht : ((Dw.p + Dw.q : ℕ) : ℤ) ≤ t) : GapGe 0 (t • hodgeWt Dw - kapBase Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [Pi.sub_apply, Pi.smul_apply, hodgeWt, GlobalTheory.CompHt.barWt, kapBase, smul_eq_mul]
  push_cast at ht ⊢
  split_ifs <;> omega

theorem gapGe_hodgeWt : GapGe 0 (hodgeWt Dw) := by
  intro τ k hk
  rw [gap_eq _ (i := ⟨k, by omega⟩) (j := ⟨k + 1, hk⟩) rfl]
  simp only [hodgeWt, GlobalTheory.CompHt.barWt]
  split_ifs <;> omega

end GlobalTheory.OrbitSep
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.hom_spec_points_levels : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  first | exact @GlobalTheory.PDForm.Lift.hom_spec | exact GlobalTheory.PDForm.Lift.hom_spec | (intros; apply GlobalTheory.PDForm.Lift.hom_spec <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.dividedPowerHomotopyOperator_values_generators : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (Q : PDPoly B) [Algebra R Q.P] [IsScalarTower R B Q.P] (η : DividedPowers (Q.ext J)) (v : Derivation R Q.P Q.P) (h : SemiHom (RingHom.id R) (algebraMap B Q.P)), Q.IsStd δ η → (∀ b, v (algebraMap B Q.P b) = 0) → (∀ n, v (Q.e (n + 1)) = Q.e n) → (∀ n, ∀ a ∈ Q.ext J, v (η.dpow (n + 1) a) = η.dpow n a * v a) → ∀ (N n : ℕ) (α : DR R B), hot v Q.e N (Q.e n • h.mDR α) = 0 ∧ (n < N → hot v Q.e N (Q.e n • (ι1 (D R Q.P (Q.e 1)) * h.mDR α)) = Q.e (n + 1) • h.mDR α) := by
  first | exact @GlobalTheory.PDForm.hot_values | exact GlobalTheory.PDForm.hot_values | (intros; apply GlobalTheory.PDForm.hot_values <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.nonempty_smoothLiftAffineThickenings : ∀ D : Data, Nonempty (Lift D) := by
  first | exact @GlobalTheory.SmoothLift.LiftEx.nonempty_lift | exact GlobalTheory.SmoothLift.LiftEx.nonempty_lift | (intros; apply GlobalTheory.SmoothLift.LiftEx.nonempty_lift <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.HotFil

theorem hot_fil : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B) (e : ℕ → B) (N : ℕ), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → (∀ k, e k ∈ fil δ k) → (∀ x y, hot v e N (x + y) = hot v e N x + hot v e N y) ∧ (∀ b, hot v e N (algebraMap B (DR R B) b) = 0) ∧ (∀ (j : ℕ), ∀ x ∈ ⋀[B]^(j + 1) Ω[B⁄R], hot v e N x ∈ ⋀[B]^j Ω[B⁄R]) ∧ (∀ x ∈ rel R δ, hot v e N x ∈ rel R δ) ∧ ∀ n, ∀ x ∈ filDR R δ n, hot v e N x ∈ filDR R δ (n + 1) := by
  intro R B _ _ _ J δ v e N hv he
  obtain ⟨hc0, -, -, -, -, hcdeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).1 R B v
  obtain ⟨-, -, -, -, -, hldeg⟩ := (GlobalTheory.T.derivationContraction_lieDerivative_deRham_rules).2 R B v
  have hrel := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).1
  have hfil := (GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2
  obtain ⟨-, -, -, -, hfil0, hanti, hsmul⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    simp only [hot, map_add (f := _), smul_add, Finset.sum_add_distrib]
  · intro b
    simp only [hot, hc0, map_zero, smul_zero, Finset.sum_const_zero]
  · intro j x hx
    have hc := hcdeg j x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ ⋀[B]^j Ω[B⁄R] := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hldeg j _ ih
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (hk k)
  · intro x hx
    have hc := (hrel R B J δ v hv x hx).1
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ rel R δ := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hrel R B J δ v hv _ ih).2
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hk k)
  · intro n x hx
    have hc := (hfil R B J δ v hv n).1 x hx
    have hk : ∀ k, (lie v ^ k) (ctr v x) ∈ filDR R δ (n - k) := by
      intro k
      induction k with
      | zero => simpa using hc
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply]
        rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
        · have : n - (k + 1) = 0 := by omega
          rw [this, hfil0]
          exact Submodule.mem_top
        · have h1 : n - k = (n - (k + 1)) + 1 := by omega
          rw [h1] at ih
          exact (hfil R B J δ v hv (n - (k + 1))).2.2 _ ih
    refine Ideal.sum_mem _ fun k _ ↦ ?_
    have hek : (-1) ^ k * e (k + 1) ∈ fil δ (k + 1) := Ideal.mul_mem_left _ _ (he (k + 1))
    exact hanti (n + 1) ((k + 1) + (n - k)) (by omega) (hsmul (k + 1) (n - k) _ hek _ (hk k))

end GlobalTheory.PDForm.HotFil
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.two_smul_pullback_symmetric_class_integral_combination : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  first | (exact @GlobalTheory.AV.QuadSum.pull_sum_smul) | (exact GlobalTheory.AV.QuadSum.pull_sum_smul) | (intros; apply GlobalTheory.AV.QuadSum.pull_sum_smul  <;> assumption)
end
