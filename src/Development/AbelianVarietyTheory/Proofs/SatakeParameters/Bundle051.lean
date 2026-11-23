module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatVec
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechHomologyEquivFam
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle006
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle045
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

namespace GlobalTheory.NatMulIsIntegralSatakeParameters

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * a) := by
  obtain ⟨y, hy0, hy'⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hy := hy' a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  rw [zsmul_eq_mul] at hy
  rcases Int.natAbs_eq y with h | h
  · rw [h] at hy
    simpa using hy
  · rw [h] at hy
    simpa using hy.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {N : ℕ}
    (Lb : Submodule (NumberField.RingOfIntegers E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (↑Lb : Set (Fin N → E))) :
    ∃ n : ℕ, 0 < n ∧ n • v ∈ Lb := by
  apply PI.WAU.B.exists_nat_L <;> assumption

end GlobalTheory.NatMulIsIntegralSatakeParameters
end

section

noncomputable section

namespace GlobalTheory.LocalInv

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ

def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ

def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)

def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig

theorem weightRegular_of_ext (B : NBC A) : WeightRegular N A := fun i P τ => by
  rw [B.embAV_inf i P]
  exact B.infW_alg _ _ τ

theorem one_lt_normV (w : PlE H) : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal))

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem r_add_le (R : Ranks) : R.r + 5 ≤ R.t := R.rank_add_five_le

theorem chi_apply (i : N.Loc) (k : ℕ) (hk : k < R.t) (g : G H.E N.Om) :
    N.chi i (k + 1) g = N.chi i 1 g * ((eps N i g) ^ k)⁻¹ := by
  rw [N.chi_def i (k + 1) (by omega) (by omega)]
  simp [eps]

theorem eps_cont (i : N.Loc) : Continuous fun g => ((eps N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((eps N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := r_add_le R
    rw [← Units.val_mul, chi_apply N i 1 (by omega)]
    simp
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem iota_eps (i : N.Loc) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    iotaO N A i ((eps N i σ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) := by
  have h := cycZ_of_isFrob (l := N.l i) hw hB hσ
  have : ((eps N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [this, h]
  simp

theorem galPol_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) :
    galPol A (A.lpSum a b) = galPol A a * galPol A b := by
  unfold galPol
  rw [A.frobEig_sum a b ha hb, Multiset.map_add (f := _), Multiset.prod_add]

theorem galPol_tw_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]

theorem galPol_tw_zero (w : PlE H) (s : ℝ) : galPol A (A.lpTw (A.lpZero w) s) = 1 := by
  unfold galPol
  rw [A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero]
  simp

theorem galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

theorem list_coe {α β : Type} (f : α → β) (L : List α) :
    (do let a ← L; pure (f a) : List β) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

theorem galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]

theorem part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk

end GlobalTheory.LocalInv
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

def Clos {R : Type} [CommRing R] (S : Subring R) (π : R) : Subring R where
  carrier := {x | ∀ n : ℕ, ∃ s ∈ S, π ^ n ∣ x - s}
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s * s', mul_mem hs hs', a * c' + s' * c, ?_⟩
    linear_combination a * hc' + s' * hc
  one_mem' := fun n => ⟨1, one_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s + s', add_mem hs hs', c + c', ?_⟩
    linear_combination hc + hc'
  zero_mem' := fun n => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha n
    obtain ⟨s, hs, c, hc⟩ := ha n
    refine ⟨-s, neg_mem hs, -c, ?_⟩
    linear_combination -hc

variable {l : ℕ} [Fact l.Prime]

def linv (l : ℕ) [Fact l.Prime] : Per.AinfP l := ((GlobalTheory.RingBasics.isUnit_l l).unit⁻¹ : (Per.AinfP l)ˣ)

theorem mul_linv : ((l : ℕ) : Per.AinfP l) * linv l = 1 := (GlobalTheory.RingBasics.isUnit_l l).mul_val_inv

def beta (ϖ : Per.Fl l) : Per.AinfP l :=
  linv l * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - 1

theorem l_mul_beta (ϖ : Per.Fl l) : ((l : ℕ) : Per.AinfP l) * beta ϖ =
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - ((l : ℕ) : Per.AinfP l) := by
  have h := mul_linv (l := l)
  rw [beta]
  linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) * h

def Sa (ϖ : Per.Fl l) : Subalgebra (Per.Ainf l) (Per.AinfP l) := Algebra.adjoin _ {beta ϖ}

def Sg (ϖ : Per.Fl l) : Subring (Per.BdRp l) :=
  (Sa ϖ).toSubring.map (algebraMap (Per.AinfP l) (Per.BdRp l))

def betaD (ϖ : Per.Fl l) : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ)

end GlobalTheory.Pst.StLat
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.cechHomologyEquivFamAlt : ∀ (R : Type) [Field R] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module R E]
    (A : Finset ι → Submodule R E) (C : GlobalTheory.Cube ι R) (g : ∀ s, C.obj s →ₗ[R] E),
    (∀ s, s.Nonempty → Function.Injective (g s)) → (∀ s, s.Nonempty → LinearMap.range (g s) = A s) →
    (∀ s t (h : s ⊆ t), s.Nonempty → ∀ x, g t (Cube.res C h x) = g s x) →
    ∀ n : ℕ, ∃ e : (cechComplex C).homology n ≃ₗ[R] (GlobalTheory.PD.cech A).H (n : ℤ),
      (∀ (z : LinearMap.ker (Cube.d C (n + 1))) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) →
        e (cechClass C n z) = Submodule.Quotient.mk w) ∧
      (∀ z : LinearMap.ker (Cube.d C (n + 1)), ∃ w : (GlobalTheory.PD.cech A).Z (n : ℤ),
        ∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (z.1 t)) ∧
      (∀ (x : Cube.Term C (n + 1)) (w : (GlobalTheory.PD.cech A).Z (n : ℤ)),
        (∀ t : {s : Finset ι // s.card = n + 1}, (w : Finset ι → E) t.1 = g t.1 (x t)) →
        Cube.d C (n + 1) x = 0) := by
  first | (exact @GlobalTheory.cechHomologyEquivFam) | (exact GlobalTheory.cechHomologyEquivFam) | (intros; apply GlobalTheory.cechHomologyEquivFam  <;> assumption)
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.laurentConstantTerm_eq_eval_origin_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ ρ : F →ₗ[k] k, IsRes k x ρ → ∃ ev : rA k x {0} →ₐ[k] k, (∀ a : rA k x {0}, ρ a = ev a) ∧ RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) := by
  first | (exact @GlobalTheory.PD.ResEv.chart0) | (exact GlobalTheory.PD.ResEv.chart0) | (intros; apply GlobalTheory.PD.ResEv.chart0 <;> assumption)
end

section

noncomputable section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.Gen.SplitAE

variable (G : GDatum)

def toCenter : 𝓞 G.F →+* Subring.center (ℚ ⊗[ℤ] G.O) where
  toFun c := ⟨(1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c, Subring.mem_center_iff.mpr fun g => by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul q o => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.commutes]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]⟩
  map_one' := by ext; simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by ext; simp [Algebra.TensorProduct.tmul_mul_tmul]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [TensorProduct.tmul_add]

theorem toCenter_isUnit (c : nonZeroDivisors (𝓞 G.F)) : IsUnit (toCenter G c) := by
  have hc0 : (c : 𝓞 G.F) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hI := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self (c : 𝓞 G.F))
    (Algebra.IsIntegral.isIntegral (R := ℤ) (c : 𝓞 G.F))
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hu : IsUnit ((k : Subring.center (ℚ ⊗[ℤ] G.O))) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap ℚ _ (k : ℚ)⁻¹,
      Subring.mem_center_iff.mpr fun g => (Algebra.commutes _ g).symm⟩, ?_⟩
    apply Subtype.ext
    show ((k : Subring.center (ℚ ⊗[ℤ] G.O)) : ℚ ⊗[ℤ] G.O) * algebraMap ℚ _ (k : ℚ)⁻¹ = 1
    rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] G.O)), ← map_mul, mul_inv_cancel₀ hk', map_one]
  have hm : toCenter G d * toCenter G c = (k : Subring.center (ℚ ⊗[ℤ] G.O)) := by
    rw [← map_mul, hd, eq_intCast (algebraMap ℤ (𝓞 G.F)) k, map_intCast]
  exact isUnit_of_mul_isUnit_right (hm ▸ hu)

def fMap : G.F →+* ℚ ⊗[ℤ] G.O :=
  (Subring.center (ℚ ⊗[ℤ] G.O)).subtype.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G))

theorem fMap_mem_center (x : G.F) : fMap G x ∈ Subring.center (ℚ ⊗[ℤ] G.O) :=
  (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G) x).2

instance instAlgebraF : Algebra G.F (ℚ ⊗[ℤ] G.O) :=
  (fMap G).toAlgebra' fun x y => ((Subring.mem_center_iff.mp (fMap_mem_center G x)) y).symm

theorem algebraMap_F_coe (c : 𝓞 G.F) :
    algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) = (1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c := by
  show fMap G (algebraMap (𝓞 G.F) G.F c) = _
  simp only [fMap, RingHom.comp_apply, IsLocalization.lift_eq]
  rfl

instance instTowerF : IsScalarTower ℚ G.F (ℚ ⊗[ℤ] G.O) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ (ℚ ⊗[ℤ] G.O)) ((algebraMap G.F (ℚ ⊗[ℤ] G.O)).comp (algebraMap ℚ G.F))
    exact congrArg (fun f : ℚ →+* ℚ ⊗[ℤ] G.O => f q) this

def ordB : Subring (ℚ ⊗[ℤ] G.O) := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom.range

end GlobalTheory.UPel.HT.Gen.SplitAE
end
end

section

noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

end GlobalTheory.WeightTwoHeckePower
end
end

section

noncomputable section

namespace GlobalTheory.Proof.HoweThetaLiftComponents

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

theorem mem_of_orthogonal_others {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (p : ι) (horth : ∀ k, k ≠ p → U k ⟂ U p)
    (x : V) (hx : ∀ k, k ≠ p → ∀ y ∈ U k, inner ℂ y x = 0) : x ∈ U p := by
  have hsup : U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    by_cases hk : k = p
    · subst hk; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ p}) => U k) k hk le_rfl)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : x ∈ U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k))
  have hle : (⨆ k ∈ {k | k ≠ p}, U k) ≤ (ℂ ∙ v)ᗮ := by
    refine iSup₂_le fun k hk y hy => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hv' : v = x - u := by rw [← huv]; abel
    rw [hv', inner_sub_right, hx k hk y hy, (horth k hk).inner_eq hy hu, sub_zero]
  have h0 : inner ℂ v v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hv)
  rw [inner_self_eq_zero] at h0
  rw [← huv, h0, add_zero]
  exact hu

theorem exists_inner_ne_zero {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ k, ∃ y ∈ U k, inner ℂ y x ≠ 0 := by
  by_contra h
  push Not at h
  have hle : (⨆ k, U k) ≤ (ℂ ∙ x)ᗮ := iSup_le fun k y hy =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h k y hy)
  rw [htop] at hle
  exact hx (inner_self_eq_zero.1
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (Submodule.mem_top : x ∈ ⊤))))

theorem eachRowHasThetaLift_of_howe :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix.ThetaGramPositiveScalar N A → (∀ i, HoweUp N A i) →
      (∀ i, TypeOrth N A i) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.EachRowHasThetaLift N A := by
  intro R H what₂ N A hpos hhowe horth
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.eachRowHasThetaLift_iff]
  rintro i σ ⟨f, hf, hf0⟩
  have hθ : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (hpos.eq_zero i σ f hf h)
  obtain ⟨P, F, hF, hFf⟩ := exists_inner_ne_zero (A.typeV i) (A.typeV_top i) _ hθ
  refine ⟨P, ⟨f, hf, hθ⟩, fun g hg => ?_⟩
  refine mem_of_orthogonal_others (A.typeV i) (A.typeV_top i) P (fun k hk => horth i k P hk) _
    fun k hk y hy => ?_
  by_contra hne
  exact hk (hhowe i σ k P ⟨g, hg, y, hy, hne⟩ ⟨f, hf, F, hF, hFf⟩)

end GlobalTheory.Proof.HoweThetaLiftComponents
end
end

section

open GlobalTheory.LatHecke

theorem _root_.GlobalTheory.T.heckeOperator_alternating_series_identity : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : Lat O K r → E) (n : ℕ) (L : Lat O K r), 1 ≤ n → ∑ k ∈ Finset.range (n + 1), ((-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2)) • heckeElem k (heckeAll (n - k) φ) L = 0 := by
  first | exact @GlobalTheory.HeckeSeries.heckeSeries_identity | exact GlobalTheory.HeckeSeries.heckeSeries_identity | (intros; apply GlobalTheory.HeckeSeries.heckeSeries_identity <;> assumption)
end

section

open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.trace_fibreRing_eq_finsum_fibrePoints : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → IsAlgClosed k → IsReduced ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) → ∀ h : (rB k K x {0}), Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) = ∑ᶠ e : fib k K x, e.1 h := by
  first | (exact @GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (exact GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib) | (intros; apply GlobalTheory.PD.FibTrace.trace_quot_eq_finsum_fib  <;> assumption)
end
