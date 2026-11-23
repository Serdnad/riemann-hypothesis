module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle498
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  first | exact @GlobalTheory.KSp.FourMem.four_mem_SB | exact GlobalTheory.KSp.FourMem.four_mem_SB | (intros; apply GlobalTheory.KSp.FourMem.four_mem_SB <;> assumption)
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

theorem _root_.GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), InCell c g ↔ ((mat c g).toBlocks₂₁).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.inCell_iff_det_ne_zero | exact GlobalTheory.KSp.inCell_iff_det_ne_zero | (intros; apply GlobalTheory.KSp.inCell_iff_det_ne_zero <;> assumption)
end

section

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def omegaDualCongr {G H : PDivGroup p O} (f : G ≅ H) : G.dual.omega ≃ₗ[O] H.dual.omega :=
  LinearEquiv.ofLinearMap (omegaDualMap G H f.hom) (omegaDualMap H G f.inv)
    (by rw [← omegaDualMap_comp, f.inv_hom_id, omegaDualMap_id])
    (by rw [← omegaDualMap_comp, f.hom_inv_id, omegaDualMap_id])

def lieCongr {G H : PDivGroup p O} (f : G ≅ H) : G.Lie ≃ₗ[O] H.Lie :=
  LinearEquiv.ofLinearMap (lieMap G H f.hom) (lieMap H G f.inv)
    (by rw [← lieMap_comp, f.inv_hom_id, lieMap_id])
    (by rw [← lieMap_comp, f.hom_inv_id, lieMap_id])

theorem datum_transport [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {h : ℕ}
    {G H : PDivGroup p O} (f : G ≅ H) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie)
    (h1 : ∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O))
    (h2 : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)) :
    ∃ (e' : H.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
      (fil' : H.dual.omega ≃ₗ[O] D.Fil) (lie' : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] H.Lie),
      (∀ t, D.al (toO e' t) = (fil' (hodgeTate H t) : Fin h → O)) ∧
        ∀ (x : H.Lie) (χ : H.dual.Tate), pairingO hε e' (bQuot D (lie'.symm x)) χ = x (dlog H χ) := by
  refine ⟨(tateCongr O f).symm ≪≫ₗ e, (omegaDualCongr f).symm ≪≫ₗ fil, lie ≪≫ₗ lieCongr f,
    fun s => ?_, fun x χ => ?_⟩
  · have := h1 (tateMap H G O f.inv s)
    change D.al (toO e (tateMap H G O f.inv s)) =
      (fil (omegaDualMap H G f.inv (hodgeTate H s)) : Fin h → O)
    rw [this, ← hodgeTate_tateMap]
  · set χ' := tateMap _ _ O (dualHom G H f.hom) χ
    have hp : ∀ y, pairingO hε ((tateCongr O f).symm ≪≫ₗ e) y χ = pairingO hε e y χ' := by
      intro y
      simp only [pairingO, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      simp only [epsPairing, tateCongr_apply, pairing_tateMap, χ']
    have hl : (lie ≪≫ₗ lieCongr f).symm x = lie.symm (lieMap H G f.inv x) := rfl
    rw [hp, hl, h2, lieMap_apply, dlog_tateMap, ← LinearMap.comp_apply (omegaMap H G f.inv),
      ← omegaMap_comp, f.inv_hom_id, omegaMap_id, LinearMap.id_apply]

theorem hasDatum_of_iso : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G H : PDivGroup p O,
      Nonempty (G ≅ H) → HasDatum hε G → HasDatum hε H := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H ⟨f⟩ hG
  haveI : IsIntegrallyClosedIn O C :=
    isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun hx => hv.exists_of_le_one
      (hv.isIntegral_iff_v_le_one.1 hx)⟩
  have hh : G.height = H.height := by
    rw [← PDivGroup.finrank_tate G C, ← PDivGroup.finrank_tate H C]
    exact (tateCongr O f).finrank_eq
  obtain ⟨D, e, fil, lie, h1, h2⟩ := hG
  unfold HasDatum
  rw [← hh]
  obtain ⟨e', fil', lie', h1', h2'⟩ := datum_transport hε f D e fil lie h1 h2
  exact ⟨D, e', fil', lie', h1', h2'⟩

end GlobalTheory.PDivLat
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem ghost_ofPadic (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (s : ℤ_[p]) :
    ghost p O n (ofPadic p O s) = padicToO p O s := by
  let g : ℤ_[p] →+* O :=
    { toFun := fun s => ghost p O n (ofPadic p O s)
      map_one' := by simp only [map_one, ghost, iterate_map_one]
      map_mul' := fun a b => by simp only [map_mul, ghost_mul]
      map_zero' := by simp only [map_zero, ghost_zero]
      map_add' := fun a b => by simp only [map_add (f := _), ghost_add] }
  exact congrArg (fun f : ℤ_[p] →+* O => f s) (padicToO_unique p O g)

theorem hodgeTate_constGen (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] :
    hodgeTate (const p O) (constGen p O) = constDlogT p O := by
  rw [hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,
    LinearMap.id_apply]

theorem latt_const_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε),
    ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    IsIdempotentElem.iff_eq_zero_or_one.1 he

  let φ : ℤ_[p] ≃ₗ[ℤ_[p]] (const p O).Tate :=
    LinearEquiv.ofBijective _ (toSpanSingleton_constGen_bijective p O hO)
  have hφ : ∀ s, φ s = s • constGen p O := fun s => rfl
  obtain ⟨eω, heω⟩ := DieudonneSandwich.exists_equiv_constDlogT (p := p) (O := O)
  let f : latt (const p O) →ₗ[Ainf p O] Ainf p O :=
    { toFun := fun y => y.1 (constGen p O)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective f ⟨fun y z h => ?_, fun a => ?_⟩, fun _ => rfl⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro t
    obtain ⟨s, rfl⟩ := φ.surjective t
    rw [hφ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    exact congrArg _ h
  · let y : TDual (const p O) :=
      { toFun := fun t => ofPadic p O (φ.symm t) * a
        map_add' := fun t t' => by rw [map_add (f := _), map_add (f := _), add_mul]
        map_smul' := fun c t => by
          rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul, mul_assoc] }
    have hy : y ∈ latt (const p O) := fun n => by
      refine ⟨ghost p O n a • eω.symm.toLinearMap, fun t => ?_⟩
      obtain ⟨s, rfl⟩ := φ.surjective t
      change ghost p O n (ofPadic p O (φ.symm (φ s)) * a) = _
      rw [LinearEquiv.symm_apply_apply, ghost_mul, ghost_ofPadic, hφ,
        hodgeTate_smul (padicToO p O), hodgeTate_constGen, LinearMap.smul_apply,
        LinearEquiv.coe_toLinearMap, map_smul, ← heω, LinearEquiv.symm_apply_apply, smul_eq_mul,
        smul_eq_mul, mul_one, mul_comm]
    refine ⟨⟨y, hy⟩, ?_⟩
    change ofPadic p O (φ.symm (constGen p O)) * a = a
    have : φ.symm (constGen p O) = 1 := φ.symm_apply_eq.2 (by rw [hφ, one_smul])
    rw [this, map_one, one_mul]

end GlobalTheory.PDivLat
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open WittVector

namespace GlobalTheory.PDivLat

section Vals

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_iterate_teichmuller (x : PreTilt O p) (n : ℕ) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] (teichmuller p x) =
      teichmuller p (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobenius_eq_map_frobenius, map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem ghost_teichmuller (n : ℕ) (x : PreTilt O p) :
    ghost p O n (teichmuller p x) = x.untilt ^ p ^ n := by
  rw [ghost, frobenius_iterate_teichmuller, fontaineTheta_teichmuller, map_pow]

theorem ghost_one (n : ℕ) : ghost p O n 1 = 1 := by
  rw [ghost, iterate_map_one, map_one]

theorem ghost_sub (n : ℕ) (a b : Ainf p O) : ghost p O n (a - b) = ghost p O n a - ghost p O n b := by
  rw [ghost, iterate_map_sub, map_sub]; rfl

theorem ghost_pow (n : ℕ) (a : Ainf p O) (k : ℕ) : ghost p O n (a ^ k) = ghost p O n a ^ k := by
  rw [ghost, iterate_map_pow, map_pow]; rfl

theorem ghost_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → Ainf p O) :
    ghost p O n (∑ i ∈ s, f i) = ∑ i ∈ s, ghost p O n (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ghost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ghost_add, ih]

theorem frobenius_ofPadic (a : ℤ_[p]) : WittVector.frobenius (ofPadic p O a) = ofPadic p O a := by
  ext k
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

end Vals

theorem ghost_values : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have h0 : PreTilt.untilt ε = 1 := hε.zeta_zero
  have h1 : PreTilt.untilt (root ε) ^ p = 1 := by
    have := zeta_succ_pow ε 0
    rw [hε.zeta_zero] at this
    exact this
  have hxi : ∀ n, ghost p O n (xi ε) = ∑ i ∈ Finset.range p, (PreTilt.untilt (root ε) ^ p ^ n) ^ i := by
    intro n
    rw [xi, ghost_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ghost_pow, ghost_teichmuller]
  refine ⟨fun a => rfl, fun n a => ?_, fun n => ?_, ?_, fun n => ?_, fun n a => ?_⟩
  · rw [ghost, Function.iterate_fixed (frobenius_ofPadic a)]
    rfl
  · rw [Sandwich.mu, ghost_sub, ghost_teichmuller, ghost_one, h0, one_pow, sub_self]
  · have hp1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
    rw [hxi, pow_zero, pow_one]
    exact hp1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  · rw [hxi, pow_succ', pow_mul, h1, one_pow]
    simp
  · rw [← ghost_frobenius, GlobalTheory.Dieudonne.frobenius_phiInv]

end GlobalTheory.PDivLat
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TermUnit

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]


omit [NumberField E] [Fintype I] in
theorem bijective_mk {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  constructor
  · intro i j hij
    have hj := InfinitePlace.mk_eq_iff.mp hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have e1 : i = k := hk i (hj.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    have e2 : j = k := hk j (Or.inl rfl)
    rw [e1, e2]
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    show InfinitePlace.mk (φ i) = w
    rcases hi with hi | hi
    · rw [← hi, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq (φ i), ← hi, InfinitePlace.mk_embedding]

theorem prod_norm_sq [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
  calc ∏ i, ‖φ i x‖ ^ 2 = ∏ w : InfinitePlace E, w x ^ InfinitePlace.mult w :=
        Fintype.prod_bijective _ (bijective_mk h) _ _ fun i => by
          rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]
    _ = _ := by rw [InfinitePlace.prod_eq_abs_norm]; push_cast; rfl

theorem prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (z : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ z = ((∏ j ∈ t, f j : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem term_unit [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x := algebraMap (OF E) E (u : OF E) with hxdef
  have hxmem : x ∈ maximalRealSubfield E := by
    rw [hxdef, IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    exact (algebraMap (OF E) (maximalRealSubfield E) u).2
  have hreal : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => by
    rw [starRingEnd_apply]
    exact (mem_maximalRealSubfield_iff x).mp hxmem (φ i)
  have hx0 : x ≠ 0 := (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  have hN : |(Algebra.norm ℚ x : ℝ)| = 1 := by
    have hv := NumberField.isUnit_iff_norm.mp (u.isUnit.map (algebraMap (OF E) (𝓞 E)))
    have hc : ((algebraMap (OF E) (𝓞 E) u : 𝓞 E) : E) = x :=
      (IsScalarTower.algebraMap_apply (OF E) (𝓞 E) E u).symm
    rw [RingOfIntegers.coe_norm, hc] at hv
    exact_mod_cast hv
  have hprod : ∏ i, ‖φ i x‖ = 1 := by
    have hsq : (∏ i, ‖φ i x‖) ^ 2 = 1 := by rw [← Finset.prod_pow, prod_norm_sq h x, hN]
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).mp hsq
  have hfac : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * starRingEnd ℂ (φ i x) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * ((s : ℂ) + σ)) := fun i => by
    have hr : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx0
    have ha : ((‖φ i x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
    have hsq : ((‖φ i x‖ : ℝ) : ℂ) ^ 2 = φ i x ^ 2 := by
      have hm := Complex.mul_conj (φ i x)
      rw [hreal, Complex.normSq_eq_norm_sq] at hm
      rw [sq (φ i x), hm]
      push_cast
      ring
    rw [show -2 * ((s : ℂ) + σ) = -((2 * s : ℕ) : ℂ) + -2 * σ by push_cast; ring,
      Complex.cpow_add _ _ ha, Complex.cpow_neg, Complex.cpow_natCast, hreal]
    congr 1
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hr, one_pow, mul_one, inv_pow, pow_mul, pow_mul, hsq]
  simp only [term]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_cpow _ _ (fun i => norm_nonneg _), hprod]
  simp

theorem norm_term [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by
  have hpos : ∀ i, 0 < ‖φ i x‖ := fun i => norm_pos_iff.mpr ((map_ne_zero (φ i)).mpr hx)
  rw [← prod_norm_sq h x, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  simp only [term, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := hpos i
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, inv_pow, ← Real.rpow_natCast _ (2 * s + κ i),
    ← Real.rpow_natCast _ (κ i), ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le]
  congr 1
  simp
  ring

private theorem term_mul' (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (y x : E) :
    term φ k κ σ (y * x) = term φ k κ σ y * term φ k κ σ x := by
  simp only [term, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, mul_inv, norm_mul, mul_pow]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

theorem term_unit_and_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    (∀ u : (OF E)ˣ, term φ (2 * s) κ σ (algebraMap (OF E) E u * x) = term φ (2 * s) κ σ x) ∧
      (x ≠ 0 → ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re))) := by
  refine ⟨fun u => ?_, fun hx => norm_term h s κ σ hx⟩
  rw [term_mul', term_unit h s κ σ u, one_mul]

end GlobalTheory.CMVal.TermUnit
end

section

open scoped NumberField

namespace GlobalTheory.TateTorsion

theorem natCard_eq_of_surj_fibres {α β γ : Type*} (g : α → β) (f : α → γ)
    (hg : Function.Surjective g) (hf : Function.Surjective f)
    (h : ∀ x y, g x = g y ↔ f x = f y) : Nat.card β = Nat.card γ := by
  refine Nat.card_congr
    { toFun := fun b => f (Function.surjInv hg b)
      invFun := fun c => g (Function.surjInv hf c)
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    have h1 := Function.surjInv_eq hf (f (Function.surjInv hg b))
    show g (Function.surjInv hf (f (Function.surjInv hg b))) = b
    rw [(h _ _).mpr h1, Function.surjInv_eq hg]
  · intro c
    have h1 := Function.surjInv_eq hg (g (Function.surjInv hf c))
    show f (Function.surjInv hg (g (Function.surjInv hf c))) = c
    rw [(h _ _).mp h1, Function.surjInv_eq hf]

theorem repr_mod_eq_zero_iff {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (l : ℕ)
    (z : M) : (∀ i, ((b.equivFun z i : ℤ) : ZMod l) = 0) ↔ ∃ y, z = l • y := by
  constructor
  · intro hz
    refine ⟨b.equivFun.symm (fun i => b.equivFun z i / (l : ℤ)), ?_⟩
    apply b.equivFun.injective
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i))]
  · rintro ⟨y, rfl⟩ i
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul]
    simp

end GlobalTheory.TateTorsion

open GlobalTheory.TateTorsion in
theorem GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  intro p hp D k _ Q _ act e I l hl hne
  haveI := D.freeLa
  haveI := D.finLa
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hl0 : 0 < l := hl.pos
  have hcop : l.Coprime p := (Nat.coprime_primes hl hp.out).mpr hne
  let b := Module.finBasisOfFinrankEq ℤ D.La D.rankLa
  let g : D.La → {q : Q // q ^ l = 1} := fun x => ⟨I.ev l x, (I.onto l hl0 hcop _).mpr ⟨x, rfl⟩⟩
  let f : D.La → (Fin (D.m * D.n * Module.finrank ℚ D.F) → ZMod l) :=
    fun x i => ((b.equivFun x i : ℤ) : ZMod l)
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := (I.onto l hl0 hcop q).mp hq
    exact ⟨x, Subtype.ext hx⟩
  have hf : Function.Surjective f := by
    intro c
    refine ⟨b.equivFun.symm (fun i => ((c i).val : ℤ)), ?_⟩
    funext i
    simp only [f, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id]
  have hgf : ∀ x y, g x = g y ↔ f x = f y := by
    intro x y
    have e1 : g x = g y ↔ I.ev l (x - y) = 1 := by
      rw [Subtype.ext_iff]
      show I.ev l x = I.ev l y ↔ _
      have : I.ev l x = I.ev l (x - y) * I.ev l y := by rw [← I.add, sub_add_cancel]
      rw [this]
      constructor
      · intro h; simpa using h
      · intro h; simp [h]
    have e2 : f x = f y ↔ ∀ i, ((b.equivFun (x - y) i : ℤ) : ZMod l) = 0 := by
      simp only [f, map_sub, Pi.sub_apply, Int.cast_sub, sub_eq_zero, funext_iff]
    rw [e1, e2, repr_mod_eq_zero_iff, I.ker l hl0 hcop]
  rw [natCard_eq_of_surj_fibres g f hg hf hgf, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
end
