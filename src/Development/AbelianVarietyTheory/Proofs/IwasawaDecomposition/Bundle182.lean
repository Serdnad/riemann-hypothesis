module

public import Formalism.LocalToGlobal.Columns.LevGSym
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle132
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle086
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfCompatibleAbelianThickenings
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

@[expose] public section

section

open Formalism.L2.Col

namespace GlobalTheory.MemXSym

open Formalism.L2.Forms

theorem facts {n k r t m rS : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1) (x : ℕ) (hx : x < n) :
    (x < r ∧ coarse r (List.replicate m t) x = 0 ∧ lvSym k rS t x = symIdx k rS x ∧ symIdx k rS x < r) ∨
    (r ≤ x ∧ lvSym k rS t x + 1 = r + coarse r (List.replicate m t) x ∧ 1 ≤ coarse r (List.replicate m t) x) := by
  rcases Nat.lt_or_ge x r with h1 | h1
  · refine Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩
    · have : x < rSym k rS := by unfold rSym; omega
      rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega
    · unfold symIdx; split_ifs <;> omega
  · refine Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩
    have hx' : ¬ x < rSym k rS := by unfold rSym; omega
    have hs : rSym k rS = r := by unfold rSym; omega
    unfold lvSym; rw [if_neg hx', hs]
    rcases Nat.lt_or_ge x (r + m * t) with h2 | h2
    · rw [GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]
    · have hx2 : x = r + m * t := by omega
      subst hx2
      rw [coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left,
        Nat.mul_div_cancel _ ht, Nat.add_assoc]

theorem facts_lt {k r t rS x : ℕ} (hr : r = k + 2 * rS + 1) (hx : x < r) :
    lvSym k rS t x = symIdx k rS x := by
  have : x < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega

theorem coarse_last {r t m x : ℕ} (hx : x < r + m * t) :
    coarse r (List.replicate m t) x < coarse r (List.replicate m t) (r + m * t) := by
  have cN : coarse r (List.replicate m t) (r + m * t) = m + 1 := by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]
  rw [cN]
  rcases Nat.lt_or_ge x r with h1 | h1
  · rw [coarse_of_lt h1]; omega
  · rw [coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega

variable {κ : Type} [Field κ]

theorem inJ_of_mem {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : M ∈ HXmsym κ n k r t m rS h) : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨hJ, hF⟩ := Subgroup.mem_inf.mp hM
  have hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := hF
  obtain ⟨hB, h0⟩ := mem_HPar.mp hJ
  have hkr : k + rS ≤ r := by omega
  rw [mem_HPsymF_iff hkr] at h0
  obtain ⟨p1, p2, p3⟩ := h0
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩
    · rw [lx, ly] at hxy
      exact p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · exfalso; omega
    · exact (mem_btG.mp hB) x y (by omega)
    · exact (mem_btG.mp hB) x y (by omega)
  · exact p2 ⟨x, by unfold rSym at hx; omega⟩
  · exact p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy
  · have hy' : y.val = r + m * t := by omega
    constructor
    · rw [hF' x y hy', Matrix.one_apply]
    · by_cases hxy : x = y
      · subst hxy; rw [hF' x x hy', Matrix.one_apply]
      · rw [if_neg hxy]
        apply (mem_btG.mp hB) y x
        have hx1 : x.val < r + m * t := by
          have := x.2; have : x.val ≠ y.val := fun e => hxy (Fin.ext e); omega
        rw [hy']
        exact coarse_last hx1

theorem mem_of_inJ {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ)) : M ∈ HXmsym κ n k r t m rS h := by
  obtain ⟨q1, q2, q3, q4⟩ := hM
  have hkr : k + rS ≤ r := by omega
  have hB : M ∈ blockUT n κ r (List.replicate m t) := mem_btG.mpr fun x y hxy => q1 x y (by
    rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)
  refine Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩
  · rw [mem_HPsymF_iff hkr]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · refine q1 (Fin.castLE h i) (Fin.castLE h j) ?_
      simp only [Fin.coe_castLE]
      rw [facts_lt hr i.2, facts_lt hr j.2]
      exact hij
    · exact q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)
    · exact q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)
  · intro x y hy
    rw [(q4 rfl x y (by omega)).1, Matrix.one_apply]

theorem memX (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t)
    (hn : n = r + m * t + 1) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t true := by
  constructor
  · intro hM
    show InJSym k rS t true _ ∧ InJSym k rS t true _
    exact ⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩
  · intro hM
    exact mem_of_inJ h hr ht hn hM.1

end GlobalTheory.MemXSym
end

section

noncomputable section

namespace GlobalTheory.KerRescale

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G Formalism.L2.Ker Classical

theorem card_eq_sum_colLen (μ : YoungDiagram) : μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  have hmap : ∀ c ∈ μ.cells, c.2 ∈ Finset.range (μ.rowLen 0) := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (0, c.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl h1
    exact YoungDiagram.mem_iff_lt_rowLen.1 h2
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (fun c hc => hmap c hc),
    Fin.sum_univ_eq_sum_range (fun c => μ.colLen c)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.colLen_eq_card]
  rfl

section Hom

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) {K : Type} [CommMonoid K] (a : Lt → K)

def wt : KM.XZ Lt N0 N1 → Additive K := Sum.elim (fun _ => 0) (fun z => Additive.ofMul (a z.1))

theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.minorXZ N0 N1 s p I) (p • Additive.ofMul (a s)) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (KM.XZ Lt N0 N1) ℤ) (Additive.ofMul (a s)) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold KM.minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => Additive.ofMul (a s))
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem Gxz_hom (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (KM.Gxz N0 N1 nu I) (∑ s, (nu s).card • Additive.ofMul (a s)) := by
  unfold KM.Gxz
  refine MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun s _ => ?_
  rw [card_eq_sum_colLen, Finset.sum_smul]
  exact MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _ fun c _ => minorXZ_hom N0 N1 a s _ (I s c)

theorem prod_of_mem_support (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) (μ : KM.XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (KM.Gxz N0 N1 nu I).support) :
    ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun z n => a z.1 ^ n) = ∏ s, a s ^ (nu s).card := by
  have h := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hμ' : μ = Finsupp.sumElim (Finsupp.sumFinsuppEquivProdFinsupp μ).1 (Finsupp.sumFinsuppEquivProdFinsupp μ).2 := by
    ext x; cases x <;> simp
  rw [hμ', Finsupp.weight_apply, Finsupp.sum_sumElim] at h
  generalize Finsupp.sumFinsuppEquivProdFinsupp μ = p at h ⊢
  have h2 := congrArg Additive.toMul h
  unfold Finsupp.sum at h2
  simp only [Function.comp_apply, wt, Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero, zero_add, toMul_sum,
    toMul_nsmul, toMul_ofMul] at h2
  exact h2

end Hom

theorem applyAt0_rescale {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (l : ℕ) [Fact l.Prime] (a : Lt → ℂ_[l])
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (nu : Lt → YoungDiagram) (I : KM.ColChoice N1 nu) :
    KM.applyAt0 N0 N1 l (MvPowerSeries.rescale (fun z => a z.1) Th) (KM.Gxz N0 N1 nu I) =
      (∏ s, a s ^ (nu s).card) • KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I) := by
  unfold KM.applyAt0
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [MvPowerSeries.coeff_rescale, prod_of_mem_support N0 N1 a nu I μ hμ, MvPolynomial.smul_monomial, smul_eq_mul]
  congr 1
  ring

theorem rescale_atLin {σ κ : Type} [Finite σ] [Fintype κ] {p : ℕ} [Fact p.Prime] (c : σ → κ → ℂ_[p]) (a : κ → ℂ_[p])
    (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.rescale a (atLin c (fun j => MvPowerSeries.X j) F) =
      atLin (fun k j => a j * c k j) (fun j => MvPowerSeries.X j) F := by
  unfold atLin
  have hs : MvPowerSeries.HasSubst (fun k : σ => ∑ j : κ, algebraMap ℂ_[p] (MvPowerSeries κ ℂ_[p]) (c k j) * MvPowerSeries.X j) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => ?_

    simp [map_sum]
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hs (MvPowerSeries.HasSubst.smul_X a)]
  congr 1
  funext k

  rw [← MvPowerSeries.rescale_eq_subst, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← MvPowerSeries.rescaleAlgHom_apply, map_smul, MvPowerSeries.rescaleAlgHom_apply,
    MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_X (MvPowerSeries.HasSubst.smul_X a)]
  show c k j • (a j • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])) = (a j * c k j) • (MvPowerSeries.X j : MvPowerSeries κ ℂ_[p])
  rw [mul_comm, mul_smul]

variable {D : D7} (P : Examples₂.EntPl D) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) (B : PlaceMatrixFamily D) {Dx : DivX D} {Tw : TwForms D}
  (a : ∀ w : D.what₂.places.Pl, D.what₂.Word → D.what₂.Tup → D.what₂.Tau → Cw D w)

theorem tauEmb_mem (w : D.what₂.places.Pl) (τ : D.what₂.Tau) (x : D.host.E) : ∃ y : D.what₂.LL, tauEmb D (P.lam w) τ x = P.iL w y := by
  have e : D.what₂.embLL (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x)) = embT D τ x := RingHom.congr_fun D.embE_φ₀ _
  refine ⟨D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG) x), ?_⟩
  rw [P.iL_lam, e]
  rfl

def adUnit (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Cw D w :=
  if AdPl D w then (lamC (P.lam w) ((O u μ).dgen τ))⁻¹ else 1

theorem norm_adUnit (hU : DgenUnitAd P O) (w : D.what₂.places.Pl) (u : D.what₂.Word) (μ : D.what₂.Tup) (τ : D.what₂.Tau) :
    ‖adUnit P O w u μ τ‖ = 1 := by
  unfold adUnit
  split_ifs with hw
  · rw [norm_inv, hU w hw u μ τ, inv_one]
  · exact norm_one

end GlobalTheory.KerRescale

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

namespace GlobalTheory.FourCopiesIso

theorem linearIndependent_of_orthogonal {K V J : Type} [Field K] [AddCommGroup V] [Module K V]
    (h : V → V →ₗ[K] K) (v : J → V) (h0 : ∀ i, h (v i) (v i) ≠ 0) (ho : ∀ i j, i ≠ j → h (v j) (v i) = 0) :
    LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  intro s g hs j hj
  have := congrArg (h (v j)) hs

  rw [map_sum, map_zero, Finset.sum_eq_single j] at this
  · rw [map_smul, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h0 j)
  · intro i _ hij
    rw [map_smul, ho i j hij, smul_zero]
  · intro e; exact absurd hj e

theorem nonempty_isoKG : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  intro K E _ _ _ _ _ cj σ ι _ hcard hσ hcc htr hpos
  classical
  let h : E → E →ₗ[K] K := fun y => (Algebra.trace K E) ∘ₗ LinearMap.mulRight K (cj y)
  have hh : ∀ x y, h y x = Algebra.trace K E (x * cj y) := fun _ _ => rfl
  have hne : ∀ x, x ≠ 0 → h x x ≠ 0 := by
    intro x hx e
    obtain ⟨a, ha, h1⟩ := hpos x hx
    rw [hh, h1] at e
    exact ha.ne' (by exact_mod_cast e)
  obtain ⟨s, hs⟩ : (⊤ : Submodule K E).FG := Module.Finite.fg_top
  obtain ⟨n, v, h0, ho, hsp⟩ := GlobalTheory.FourCopies.exists_orthogonal_family h
    (fun x y e => by
      rw [hh] at e ⊢
      have := htr (x * cj y)
      rw [e, map_zero, map_mul, hcc, mul_comm] at this
      exact this)
    (fun x e => by
      by_contra hx
      exact hne x hx e) s
  have htop : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hs]; exact Submodule.span_le.2 (fun y hy => hsp y hy)
  have hli := linearIndependent_of_orthogonal h v (fun i => hne _ (h0 i)) ho
  have hn : Module.finrank K E = n := by
    simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq (hcard.trans hn)
  choose a ha hav using fun i => hpos (v i) (h0 i)
  choose A hA hA' using fun i => GlobalTheory.FourCopies.exists_similitude (a i) (ha i)
  let H : (Fin 4 → E) → (Fin 4 → E) →ₗ[K] K := fun y => ∑ k, h (y k) ∘ₗ LinearMap.proj k
  have hH : ∀ x y, H y x = ∑ k, Algebra.trace K E (x k * cj (y k)) := by
    intro x y
    simp only [H, LinearMap.sum_apply]
    rfl
  let b : Fin 4 × ι → (Fin 4 → E) := fun w k => (A (e w.2) w.1 k : E) * v (e w.2)
  have hb : ∀ w w', H (b w') (b w) = if w = w' then 1 else 0 := by
    intro w w'
    have h1 : H (b w') (b w) =
        ((∑ k, A (e w.2) w.1 k * A (e w'.2) w'.1 k : ℚ) : K) * h (v (e w'.2)) (v (e w.2)) := by
      rw [hH, hh]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← smul_eq_mul (_ * _ : K), ← map_smul, Algebra.smul_def]
      congr 1
      simp only [b, map_mul, map_ratCast]
      ring
    rw [h1]
    by_cases hi : w.2 = w'.2
    · rw [← hi, hh, hav, ← Rat.cast_mul, mul_comm, hA]
      have : w.1 = w'.1 ↔ w = w' := ⟨fun t => Prod.ext t hi, fun t => by rw [t]⟩
      simp only [this]
      split_ifs <;> simp
    · have : w ≠ w' := fun t => hi (by rw [t])
      rw [if_neg this, ho _ _ (fun t => hi (e.injective t)), mul_zero]
  have hbl : LinearIndependent K b :=
    linearIndependent_of_orthogonal H b (fun i => by rw [hb]; simp) (fun i j hij => by rw [hb, if_neg hij])
  have : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  have hc : Fintype.card (Fin 4 × ι) = Module.finrank K (Fin 4 → E) := by
    rw [Module.finrank_pi_fintype, Fintype.card_prod, hcard]; simp
  let B := basisOfLinearIndependentOfCardEqFinrank hbl hc
  have hB : ∀ w, B w = b w := fun w => by simp [B]
  have hco : ∀ x w, H (b w) x = B.equivFun x w := by
    intro x w
    conv_lhs => rw [← B.sum_equivFun x]

    simp only [map_sum, map_smul, hB, hb, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  refine ⟨⟨B.equivFun, fun x y => ?_⟩⟩
  have hy : ∀ k, cj (y k) = ∑ w, algebraMap K E (σ (B.equivFun y w)) * cj (b w k) := by
    intro k
    conv_lhs => rw [← B.sum_equivFun y]

    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hB]
    simp only [Algebra.smul_def, map_mul, hσ]

  simp only [hσ, ← map_mul, ← map_sum]
  congr 1

  simp only [hy, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← hco x w, hH, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← smul_eq_mul (σ _), ← map_smul, Algebra.smul_def]
  congr 1
  ring

end GlobalTheory.FourCopiesIso
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionLimitSq

section Flat

variable {X Y Z : Scheme.{0}} {L : LB X}

theorem good_sq_iff (z : Z) (J' : (Z ⟶ X) → L.ι) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) z (fun ψ _ => J' ψ) ↔ Good L z J' := by
  constructor
  · intro h ψ
    have := GlobalTheory.Algebraise.mem_wc.1 (h ψ)
    simpa using this
  · intro h ψ
    exact GlobalTheory.Algebraise.mem_wc.2 (by simpa using h ψ)

theorem eq_const_of_fin_one {α β : Type} (J : α → (Fin 1 → β)) : J = fun ψ _ => J ψ 0 :=
  funext fun ψ => funext fun κ => congrArg (J ψ) (Subsingleton.elim _ _)

theorem sval_flat {a n m : ℤ} {g : Y ⟶ X} {t : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))}
    {s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g)
      (fun _ => n))}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j →
      gs r z _ (t.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j))
    (r : Z ⟶ Y) (z : Z) (J' : (Z ⟶ X) → L.ι) (hJ : Good L z J') :
    sval t r z J' = sval s r z (fun ψ _ => J' ψ) :=
  h Z r z (J' (r ≫ g)) (by simpa using hJ (r ≫ g))

end Flat

theorem existsUnique_sec_of_compatible_sq : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (s e) r z J) → ∃! σ : H0 (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)).ι), Good (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => 2)) z J → sval σ (r ≫ (fstG I e P.A).left) z J = sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hm : (((2 * n : ℕ) : ℤ)) = 2 * (n : ℤ) := by push_cast; ring
  have hn2 : 1 ≤ 2 * n := by omega
  choose t ht using fun e => GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (fstG I e P.A).left (s e)
  have htc : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι),
      Good P.L z J → sval (t (e + 1)) (r ≫ thickMap R I e P.A) z J = sval (t e) r z J := by
    intro e Z r z J hJ
    rw [sval_flat (ht (e + 1)) _ z J hJ, sval_flat (ht e) r z J hJ]
    exact hs e Z r z _ ((good_sq_iff z J).2 hJ)
  obtain ⟨σ₀, hσ₀, hσ₀u⟩ := GlobalTheory.SectionLimit.existsUnique_sec_of_compatible hS R I P (2 * n) hn2 t htc
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.linComb_pow_section_unflatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ₀
  refine ⟨σ, fun e Z r z J hJ => ?_, fun σ' hσ' => ?_⟩
  · obtain ⟨J', rfl⟩ : ∃ J' : (Z ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff z J').1 hJ
    rw [← sval_flat hσ _ z J' hJ', hσ₀ e Z r z J' hJ', sval_flat (ht e) r z J' hJ']
  · obtain ⟨τ, hτ⟩ := GlobalTheory.T.linComb_pow_section_flatten P.L 2 (n : ℤ) ((2 * n : ℕ) : ℤ) hm (𝟙 P.A.left) σ'
    have hτσ : τ = σ₀ := hσ₀u τ fun e Z r z J hJ => by
      rw [sval_flat hτ _ z J hJ, hσ' e Z r z _ ((good_sq_iff z J).2 hJ), ← sval_flat (ht e) r z J hJ]
    have hL := LB.isLB_linComb P.isLB (K := Fin 1) (fun _ => 𝟙 P.A.left) (fun _ => (2 : ℤ))
    refine DVR.SecOps.sec_ext (sec_ext_val hL fun y J hJ => ?_)
    obtain ⟨J', rfl⟩ : ∃ J' : (P.A.left ⟶ P.A.left) → P.L.ι, J = fun ψ _ => J' ψ := ⟨_, eq_const_of_fin_one J⟩
    have hJ' := (good_sq_iff y J').1 hJ
    rw [← sval_flat hτ _ y J' hJ', ← sval_flat hσ _ y J' hJ', hτσ]

end GlobalTheory.SectionLimitSq
end
end
