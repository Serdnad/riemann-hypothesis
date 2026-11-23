module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle271
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMapEntriesHaarUnitriangularEqSmulPi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle272
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import ReciprocityTheory.BasicDefinitions.ExistsUnique
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001

@[expose] public section

section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

open Formalism.MainNotions.N (twistRep coefRep)

namespace GlobalTheory.AdmLoc

theorem mk_mem_H1fX_iff_inHfX {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ) :
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  intro hρ hT z hz
  have e1 : ρ' = twistRep ρ (chiLL LL χ⁻¹) := by
    ext g v
    rw [hρ g, twistRep_apply]
    simp [chiLL, tableLineDegreeTwo.charL]
  subst e1
  have e2 : L' = twLattice L χ⁻¹ := by
    cases L'
    simp only at hT
    subst hT
    rfl
  subst e2
  have hact : ∀ g (m : ↥L.T ⊗[O] X), twCoef (latRep L) χ X g m = tableLineDegreeTwo.actTw L X χ g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [coefRep_tmul, twistRep_apply]
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, smul_tmul']
      rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hA : toAmb (twCoef (latRep L) χ X) (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk z := rfl
  rw [finiteSelmer, Submodule.mem_comap, hA, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
    have hrep : ∀ p : ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹)), ∃ c : ↥(latticeCocycles (twLattice L χ⁻¹)),
        (c : G → V) ∈ latticeFiniteCocycles PD (twLattice L χ⁻¹) ∧ Submodule.Quotient.mk c = (p : LatticeCohomology (twLattice L χ⁻¹)) := by
      rintro ⟨p, hp⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hp
      exact ⟨c, hc, rfl⟩
    choose rep hrepf hrepmk using hrep
    let e := S.equivFin
    let cc : Fin S.card → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => rep (e.symm j).1.1
    let xx : Fin S.card → X := fun j => (e.symm j).1.2
    have key : (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        (∑ p ∈ S, p.1 ⊗ₜ[O] p.2) = Submodule.Quotient.mk (∑ j, tensCoc L χ X (cc j) (xx j)) := by

      rw [map_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Eq.trans ?_ (map_sum (Submodule.mkQ _) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hrepmk, tensAmb_tmul]
      rfl
    rw [key] at hu
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.eq _).mp hu
    refine ⟨S.card, fun j g => evT (twLattice L χ⁻¹) g (cc j), xx, -m, fun j => hrepf _, fun g => ?_⟩
    have h1 : twCoef (latRep L) χ X g m - m = (∑ j, tensCoc L χ X (cc j) (xx j)) g - z g := congrFun hm g
    simp only [Finset.sum_apply] at h1
    rw [hact] at h1
    simp only [map_neg]
    have h2 : ∀ j, tensCoc L χ X (cc j) (xx j) g = evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j := fun j => rfl
    simp only [h2] at h1
    have h3 : z g = ∑ j, evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j - (tableLineDegreeTwo.actTw L X χ g m - m) := by
      rw [h1]; abel
    rw [h3]
    abel
  · rintro ⟨k, c, x, m, hc, hzc⟩
    let cc : Fin k → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => ⟨fun g => (c j g : V), (hc j).1⟩
    refine ⟨∑ j, (⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
      ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j, ?_⟩

    rw [map_sum]
    have h1 : ∀ j, (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        ((⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
          ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j) = Submodule.mkQ _ (tensCoc L χ X (cc j) (x j)) := fun j => rfl
    simp only [h1]

    rw [← map_sum, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    refine Submodule.mem_map.mpr ⟨-m, Submodule.mem_top, ?_⟩
    funext g
    change twCoef (latRep L) χ X g (-m) - (-m) = (∑ j, tensCoc L χ X (cc j) (x j)) g - z g
    simp only [Finset.sum_apply, hact, map_neg, hzc g]
    have h2 : ∀ j, tensCoc L χ X (cc j) (x j) g = c j g ⊗ₜ[O] x j := fun j => rfl
    simp only [h2]
    abel

end GlobalTheory.AdmLoc
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.PolarBound

theorem card_le_sum {k V ι : Type} [Field k] [AddCommGroup V] [Module k V] [Fintype ι] {s : ℕ}
    (c : ι → Fin s → V) (N : ι → Submodule k V) (d : ι → ℕ)
    (hd : ∀ i, Module.finrank k (↥(LinearMap.range (Fintype.linearCombination k (c i))) ⧸
      (N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))) ≤ d i)
    (hinj : ∀ t : Fin s → k, (∀ i, ∑ a, t a • c i a ∈ N i) → t = 0) : s ≤ ∑ i, d i := by
  let f := LinearMap.pi fun i => ((N i).submoduleOf (LinearMap.range (Fintype.linearCombination k (c i)))).mkQ ∘ₗ
    (Fintype.linearCombination k (c i)).rangeRestrict
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro t ht
    refine hinj t fun i => ?_
    have h1 : f t i = 0 := congrFun ht i
    exact (Submodule.Quotient.mk_eq_zero ((N i).submoduleOf
      (LinearMap.range (Fintype.linearCombination k (c i))))).1 h1
  have h2 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h2
  exact h2.trans (Finset.sum_le_sum fun i _ => hd i)

variable {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem cob_mem (D : ModPG R n (Vc k m)) (y : ZMod n → Vc k m) :
    ((fun i => D.φ i (y (i - 1)) - y i, fun i => D.γ i (y i) - y i) :
      (ZMod n → Vc k m) × (ZMod n → Vc k m)) ∈ herrB D := ⟨y, rfl⟩

theorem gauge_one (D : ModPG R n (Vc k m)) (Dt : TopData n m) (N : Lats k n m)
    (hI : ∀ i, (Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i)
    (hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i) (hN : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i (a : ℕ), a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0)
    (z : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : InZZ D Dt N z.1 z.2) :
    ∃ (z' : (ZMod n → Vc k m) × (ZMod n → Vc k m)) (c : ZMod n → Vc k m), z - z' ∈ herrB D ∧
      ∀ i, D.γ i (z'.1 i) - z'.1 i = D.φ i (z'.2 (i - 1)) - z'.2 i ∧ z'.2 i ∈ sh (Dt.sg l i + 3) (N i) ∧
        c i - z'.1 i ∈ N i ∧
        (Dt.ty i = LType.G → c i ∈ sh (-Dt.w i) (N i) ∧ D.γ i (c i) - c i ∈ sh 1 (N i)) ∧
        (Dt.ty i = LType.Bd → c i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
          D.γ i (c i) - c i ∈ sh (Dt.wst i + 2) (N i)) := by
  obtain ⟨b, g⟩ := z
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl2 : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  obtain ⟨y, hy, hy'⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
    (fun i => by have := hI i; have := (hw i).2; unfold TopData.wst at this; omega) hsen b g
    (fun i => (hz i).1) (fun i => (hz i).2.1)).1
  have hx : ∀ i, ∃ x ∈ N i, (Dt.ty i = LType.G → x = y i) ∧
      (Dt.ty i = LType.Bd → g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i)) := by
    intro i
    cases h : Dt.ty i with
    | G => exact ⟨y i, hy i, fun _ => rfl, fun h => by cases h⟩
    | Bd =>
      obtain ⟨x, hx, hx'⟩ := ((hz i).2.2.2 h).2
      exact ⟨x, hx, fun h => (by cases h), fun _ => hx'⟩
  choose x hx hxG hxB using hx
  refine ⟨(fun i => b i - (D.φ i (y (i - 1)) - y i), fun i => g i - (D.γ i (y i) - y i)),
    fun i => b i - D.φ i (y (i - 1)) + x i, ?_, fun i => ?_⟩
  · convert cob_mem D y using 1
    ext i : 2 <;> simp
  have h0 : D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i := (hz i).1
  have hφ : D.φ i (y (i - 1)) ∈ pull (D.φ i) (N (i - 1)) := Submodule.subset_span ⟨_, hy _, rfl⟩
  have hdeep : D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) ∈ sh (Dt.wst i + 2) (N i) := by
    have h1 := Gauge.phi_sh R _ (D.φ_semi i) _ _ _ (hAB i).1 (Dt.sg l (i - 1) + 3)
      (x := g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) (by simpa using hy' (i - 1))
    refine sh_le_sh_of_le ?_ _ h1
    have := hI i
    unfold TopData.wst
    push_cast; nlinarith
  have hc : D.γ i (b i - D.φ i (y (i - 1)) + x i) - (b i - D.φ i (y (i - 1)) + x i) =
      D.φ i (g (i - 1) - (D.γ (i - 1) (y (i - 1)) - y (i - 1))) - (g i - (D.γ i (x i) - x i)) := by
    simp only [map_sub, map_add (f := _), D.comm]
    linear_combination (norm := module) h0
  have hsh : ∀ (a : ℤ) (P : Submodule k⟦X⟧ (Vc k m)), 0 ≤ a → P ≤ sh (-a) P := fun a P ha => by
    simpa [sh_zero_eq] using sh_le_sh_of_le (a := 0) (b := -a) (by omega) P
  refine ⟨?_, hy' i, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩
  · simp only [map_sub, D.comm]
    linear_combination (norm := module) h0
  · convert (N i).sub_mem (hx i) (hy i) using 1
    simp only []
    abel
  · exact Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.1 h) ((hAB i).1 hφ)) (hsh _ _ (hw i).1 (hx i))
  · beta_reduce
    rw [hc, hxG i h]
    refine Submodule.sub_mem _ (sh_le_sh_of_le ?_ _ hdeep) (sh_le_sh_of_le ?_ _ (hy' i))
    · have := (hw i).2; omega
    · omega
  · refine Submodule.add_mem _ (Submodule.sub_mem _ ((hz i).2.2.2 h).1 (hsh _ _ (hw i).2 hφ)) ?_
    have := sh_le_sh (-Dt.wst i) (hAB i).2
    rw [sh_sh_eq, neg_add_cancel, sh_zero_eq] at this
    exact this (hx i)
  · beta_reduce
    rw [hc]
    exact Submodule.sub_mem _ hdeep (hxB i h)


omit [Fact l.Prime] [CharP k l] [NeZero n] in
theorem span_prop {s : ℕ} (c : Fin s → Vc k m) (g : Vc k m →ₗ[k] Vc k m) (P Q : Submodule k⟦X⟧ (Vc k m))
    (h : ∀ a, c a ∈ P ∧ g (c a) - c a ∈ Q) :
    ∀ x ∈ LinearMap.range (Fintype.linearCombination k c), x ∈ P ∧ g x - x ∈ Q := by
  rintro _ ⟨t, rfl⟩

  rw [Fintype.linearCombination_apply, map_sum, ← Finset.sum_sub_distrib]
  refine ⟨Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (h a).1,
    Submodule.sum_mem _ fun a _ => ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_of_tower_mem _ _ (h a).2

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n m) (N : Lats k n m), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ABC D Dt.w Dt.wst N → (∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = m ∧ EPoly (D.γ i) (N i) (Dt.wst i + 1))) → ∀ (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)), (∀ a, InZZ D Dt N (z a).1 (z a).2) → LinearIndependent k (fun a => (herrB D).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hΨ k _ l n m _ _ _ R D ι Dt N hι T1 T2 T3 hN hs s z hz hli
  have hW := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3
  have hw : ∀ i, 0 ≤ Dt.w i ∧ 0 ≤ Dt.wst i := fun i => by
    have h1 := Dt.one_le_letterBlockLength
    have := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
    unfold TopData.wst
    omega
  choose z' c hz' hc using fun a => gauge_one D Dt N (fun i => (hW i).1) hw hN (fun i => (hs i).1) (z a) (hz a)
  obtain ⟨hL, hAB, hC⟩ := hN
  have hl5 : 5 ≤ l := by have := T1 0; omega
  obtain ⟨ψ, -, ⟨p1, p2, -, p4⟩, hmod⟩ := hΨ.modPG l k hl5 R ι hι
  choose Ψ hΨ1 hΨ2 hΨ3 using fun i => hmod n (Vc k m) D i
  refine card_le_sum (fun i a => c a i) (fun i => (N i).restrictScalars k) Dt.d (fun i => ?_) (fun t ht => ?_)
  · cases h : Dt.ty i with
    | G =>
      have e : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (hw i).1
      have := GlobalTheory.T.gammaMinusOneDivVariable_polar_kernel_le_senWeights R (D.γ i) (D.γ_semi i) (N i) (hL i) (hC i) (Dt.w i).toNat
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (fun x hx => by
          have := span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.1 h) x hx
          rw [e]
          refine ⟨this.1, ?_⟩
          have h2 := mem_sh_iff_smul_mem.1 this.2
          rwa [zpow_neg_one] at h2)
      rw [e, (hs i).2.1 h] at this
      exact this
    | Bd =>
      have e : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (hw i).2
      obtain ⟨-, -, w1, w2⟩ := (hW i).2.2.2 h
      have h1 := Dt.one_le_letterBlockLength
      have h2 := T1 i
      have h3 := (hW i).1
      obtain ⟨s1, s2⟩ := (hs i).2.2 h
      have := GlobalTheory.T.polarPart_finrank_add_senWeights_le_rank R D Ψ ψ hΨ1 p1 (by simpa using p2 1) hΨ2
        (fun a ha ha' => by rw [p4 a ha ha']; ext x; simp [eq_comm]) i (N (i - 1)) (N i) (Dt.wst i).toNat
        (Dt.sg l (i - 1)) (Dt.w i) (hL _) (hL _) (hC _) (hC _) (by omega) (by omega) (by rw [e]; exact (hAB i).2)
        (hAB i).1 (by rw [e]; unfold TopData.wst; nlinarith) (hs _).1
        (fun y hy hy0 => by
          rw [e] at hy ⊢
          have h4 := (hΨ3 i _ (hL (i - 1))).2 (hC _) (-Dt.wst i) (by omega) (by omega)
          have h5 : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.kerPsi (Ψ i) (pull (D.φ i) (N (i - 1))) (-Dt.wst i + 1) :=
            ⟨by rwa [neg_add_eq_sub], hy0⟩
          rw [← h4] at h5
          obtain ⟨x, ⟨hx, hx0⟩, hxy⟩ := h5
          exact ⟨x, hx, hx0, hxy⟩)
        (by rw [e]; exact GlobalTheory.T.gammaNabla_mem_of_killing_polynomial D i (N i) _ (hC i) s2)
        (LinearMap.range (Fintype.linearCombination k fun a => c a i)) (by
          rw [e]; exact span_prop _ (D.γ i) _ _ (fun a => (hc a i).2.2.2.2 h))
      rw [Module.finrank_fin_fun] at this
      omega
  · have hg : ∀ i, (∑ a, t a • z' a).2 i ∈ sh (Dt.sg l i + 3) (N i) := fun i => by
      simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.1
    obtain ⟨y, -, hy⟩ := (Gauge.main R D Dt.w Dt.wst (Dt.sg l) N hL hAB hC
      (fun i => by have := (hW i).1; have := (hw i).2; unfold TopData.wst at this; omega) (fun i => (hs i).1)
      (∑ a, t a • z' a).1 (∑ a, t a • z' a).2 (fun i => by

        simp only [Prod.snd_sum, Prod.fst_sum, Finset.sum_apply, Prod.smul_snd, Prod.smul_fst, Pi.smul_apply,
        map_sum, map_smul, ← Finset.sum_sub_distrib, ← smul_sub]
        exact Finset.sum_congr rfl fun a _ => by rw [(hc a i).1])
      (fun i => sh_le_sh_of_le (by omega) _ (hg i))).2 hg (fun i => by
        have h1 : ∑ a, t a • (c a i - (z' a).1 i) ∈ N i :=
          Submodule.sum_mem _ fun a _ => Submodule.smul_of_tower_mem _ _ (hc a i).2.2.1
        have h2 : ∑ a, t a • c a i ∈ N i := ht i
        convert (N i).sub_mem h2 h1 using 1
        simp only [Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, ← Finset.sum_sub_distrib,
          ← smul_sub, sub_sub_cancel])
    have h1 : ∑ a, t a • z' a ∈ herrB D := by
      convert cob_mem D y using 1
      exact Prod.ext (funext fun i => (hy i).1) (funext fun i => (hy i).2)
    have h2 : ∑ a, t a • (z a - z' a) ∈ herrB D :=
      Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hz' a)
    have h3 : ∑ a, t a • z a ∈ herrB D := by
      convert (herrB D).add_mem h1 h2 using 1
      simp only [← Finset.sum_add_distrib, ← smul_add, add_sub_cancel]
    funext a
    refine Fintype.linearIndependent_iff.1 hli t ?_ a
    have h4 : (herrB D).mkQ (∑ a, t a • z a) = 0 := (Submodule.Quotient.mk_eq_zero _).2 h3

    simpa only [map_sum, map_smul] using h4

end GlobalTheory.Models.PolarBound
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.SubModel

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (g : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hg : IsHom A B g) :
    ∃ (K : Ob k G) (i : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A i ∧ Function.Injective i ∧ Function.Exact i g := by
  have hst : ∀ s : G, LinearMap.ker g ≤ (LinearMap.ker g).comap (A.ρ s) := by
    intro s x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker] at hx ⊢
    rw [hg, hx, map_zero]
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker g) hst)
  refine ⟨K, (LinearMap.ker g).subtype ∘ₗ e.symm.toLinearMap, ?_, ?_, ?_⟩
  · intro s x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simp [Representation.subrepresentation]
  · exact (LinearMap.ker g).injective_subtype.comp e.symm.injective
  · intro y
    constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hf : IsHom A B f) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact f q := by
  have hst : ∀ s : G, LinearMap.range f ≤ (LinearMap.range f).comap (B.ρ s) := by
    rintro s _ ⟨x, rfl⟩
    exact ⟨A.ρ s x, hf s x⟩
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range f) hst)
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range f).mkQ, ?_, ?_, ?_⟩
  · intro s x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    simp [Representation.quotient]
  · exact e.surjective.comp (LinearMap.range f).mkQ_surjective
  · intro y
    simp [Submodule.Quotient.mk_eq_zero]

theorem IsHom.comp' {A B C : Ob k G} {f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)}
    {g : (Fin B.m → k) →ₗ[k] (Fin C.m → k)} (hf : IsHom A B f) (hg : IsHom B C g) : IsHom A C (g ∘ₗ f) := by
  intro s x
  simp only [LinearMap.comp_apply]
  rw [hf, hg]

theorem model_pre : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m), IsHom A B f → Function.Injective f → M.Model B N → M.Model A (F.pre A B f N) := by
  intro k G _ _ l n _ _ _ R F r Dt M A B f N hf hfi hN
  obtain ⟨C, Nb, A₁, j, p, hb, hj, hji, hp, hps, rfl⟩ := hN
  obtain ⟨Q, q, hq, hqs, hfq⟩ := exists_coker A B f hf
  have hqp : IsHom A₁ Q (q ∘ₗ p) := IsHom.comp' hp hq
  obtain ⟨K, i, hi, hii, hex⟩ := exists_ker A₁ Q (q ∘ₗ p) hqp
  have hr : ∀ x, (p ∘ₗ i) x ∈ LinearMap.range f := fun x => (hfq _).1 ((hex _).2 ⟨x, rfl⟩)
  let p' : (Fin K.m → k) →ₗ[k] (Fin A.m → k) :=
    (LinearEquiv.ofInjective f hfi).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (p ∘ₗ i) hr
  have hfp : ∀ x, f (p' x) = p (i x) := by
    intro x
    have := congrArg Subtype.val ((LinearEquiv.ofInjective f hfi).apply_symm_apply
      (LinearMap.codRestrict _ (p ∘ₗ i) hr x))
    exact this
  have hp' : IsHom K A p' := by
    intro s x
    apply hfi
    rw [hfp, hf, hfp, hi, hp]
  have hp's : Function.Surjective p' := by
    intro a
    obtain ⟨y, hy⟩ := hps (f a)
    have : (q ∘ₗ p) y = 0 := by
      rw [LinearMap.comp_apply, hy]
      exact (hfq _).2 ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (hex _).1 this
    exact ⟨x, hfi (by rw [hfp, hy])⟩
  have oC : F.Obj C := M.base_obj _ _ hb
  have o1 : F.Obj A₁ := F.obj_sub _ _ _ hj hji oC
  have oB : F.Obj B := F.obj_quot _ _ _ hp hps o1
  have oA : F.Obj A := F.obj_sub _ _ _ hf hfi oB
  have oK : F.Obj K := F.obj_sub _ _ _ hi hii o1
  have oQ : F.Obj Q := F.obj_quot _ _ _ hq hqs oB
  have hcomm : f ∘ₗ p' = p ∘ₗ i := LinearMap.ext hfp
  have hsq : ∀ a x, F.map A B f a (F.map K A p' a x) = F.map A₁ B p a (F.map K A₁ i a x) := by
    intro a x
    have h1 := F.map_comp K A B p' f oK oA oB hp' hf a
    have h2 := F.map_comp K A₁ B i p oK o1 oB hi hp a
    rw [hcomm, h2] at h1
    exact (LinearMap.congr_fun h1 x).symm
  have e1 := GlobalTheory.T.exact_map_of_exact F A B Q f q oB hf hq hfi hqs hfq
  have e2 := GlobalTheory.T.exact_map_of_exact F K A₁ Q i (q ∘ₗ p) o1 hi hqp hii (hqs.comp hps) hex
  refine ⟨C, Nb, K, j ∘ₗ i, p', hb, IsHom.comp' hi hj, hji.comp hii, hp', hp's, ?_⟩
  funext a
  ext x
  simp only [DFun.pre, DFun.push, Submodule.mem_comap, Submodule.mem_map, LinearMap.restrictScalars_apply,
    F.map_comp K A₁ C i j oK o1 oC hi hj a, LinearMap.comp_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : F.map A₁ Q (q ∘ₗ p) a y = 0 := by
      rw [F.map_comp A₁ B Q p q o1 oB oQ hp hq a, LinearMap.comp_apply, hyx]
      exact (e1 a _).2 ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := (e2 a _).1 this
    exact ⟨z, hy, F.map_inj A B f oA oB hf hfi a (by rw [hsq, hyx])⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, hz, (hsq a z).symm⟩

end GlobalTheory.Models.SubModel
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μR : Measure R) [μR.IsAddHaarMeasure]
    (ν : Measure (GlobalTheory.SmGL.unipB R (Fin n))) [ν.IsHaarMeasure],
    ∃ c : ℝ≥0∞, Measure.map (fun (u : GlobalTheory.SmGL.unipB R (Fin n)) (p : {p : Fin n × Fin n // p.1 < p.2}) =>
        ((u : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p.1.1 p.1.2) ν = c • Measure.pi (fun _ => μR) := by
  first | exact @GlobalTheory.UnipCoord.map_coords_haar | exact GlobalTheory.UnipCoord.map_coords_haar | (intros; apply GlobalTheory.UnipCoord.map_coords_haar <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_cutoff_function_torus_GL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ f' : Gl r F → ℂ, IsTest f' → ∃ α : GL (Fin r) F → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : GL (Fin r) F, (∃ v w : Fin r → F, f' ((g : Matrix (Fin r) (Fin r) F) * companion p * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), v, w, lam) ≠ 0) → ∀ s₀ : A.Kˣ, ∫ s, α (g * LinDesc.tm A hG s₀ * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1 := by
  first | exact @GlobalTheory.JR.LinDesc.exists_cutoff_torus | exact GlobalTheory.JR.LinDesc.exists_cutoff_torus | (intros; apply GlobalTheory.JR.LinDesc.exists_cutoff_torus <;> assumption)
end
