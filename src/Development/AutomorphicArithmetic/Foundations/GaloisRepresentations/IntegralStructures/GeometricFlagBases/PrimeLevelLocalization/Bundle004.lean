module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle004
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PJSurj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TraceMapUnipotent
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (Plc GLw)
open UpperTheory.Gal.Int.Geo.Pl
open scoped Classical Topology

private lemma v_coe_algebraMap {E : Type} [Field E] [NumberField E] (w : Plc E) (c : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = w.intValuation c := by
  have h : ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) c : w.adicCompletionIntegers E) : w.adicCompletion E)
      = algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E c) := rfl
  rw [h]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w (algebraMap (𝓞 E) E c)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  exact this

private lemma v_le_of_inId {E : Type} [Field E] [NumberField E] (w : Plc E) (e : ℕ)
    (y : w.adicCompletion E) (h : InId w (w.asIdeal ^ e) y) : Valued.v y ≤ WithZero.exp (-(e : ℤ)) := by
  obtain ⟨z, hz, rfl⟩ := h
  refine Submodule.span_induction
    (p := fun (z : w.adicCompletionIntegers E) _ => Valued.v (z : w.adicCompletion E) ≤ WithZero.exp (-(e : ℤ)))
    ?_ ?_ ?_ ?_ (show z ∈ Submodule.span _ _ from hz)
  · rintro _ ⟨c, hc, rfl⟩
    rw [v_coe_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem w c e).2 hc
  · simp
  · intro a b _ _ ha hb
    have := Valuation.map_add_le (Valued.v) ha hb
    simpa using this
  · intro a b _ hb
    have ha : Valued.v (a : w.adicCompletion E) ≤ 1 := a.2
    simp only [smul_eq_mul, MulMemClass.coe_mul, map_mul]
    exact mul_le_of_le_one_of_le ha hb

private lemma v_inv_sub_one_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (g : GLw n w)
    (hg : g ∈ KGL w (n := n)) (γ : WithZero (Multiplicative ℤ))
    (h : ∀ i k, Valued.v ((g.val - 1) i k) ≤ γ) (i k : Fin n) :
    Valued.v (((g⁻¹).val - 1) i k) ≤ γ := by
  have hI := ((GlobalTheory.HenQ.Basic.mem_KGL_iff w g).1 hg).2
  have e : (g⁻¹).val - 1 = -((g⁻¹).val * (g.val - 1)) := by
    rw [mul_sub, mul_one, Units.inv_mul]
    abel
  rw [e, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hI i j) (h j k)

private lemma tendsto_of_v_le {E : Type} [Field E] [NumberField E] (w : Plc E)
    (y : ℕ → w.adicCompletion E) (c : w.adicCompletion E)
    (h : ∀ e : ℕ, Valued.v (y e - c) ≤ WithZero.exp (-(e : ℤ))) : Filter.Tendsto y Filter.atTop (𝓝 c) := by
  rw [← tendsto_sub_nhds_zero_iff, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  obtain ⟨m, hm⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hne)
  filter_upwards [Filter.eventually_ge_atTop m] with e he
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt ((h e).trans ?_) hm
  rw [← WithZero.exp_nsmul, WithZero.exp_le_exp]
  simpa using he

private lemma tendsto_mat_of_v_le {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E)
    (M : ℕ → Matrix (Fin n) (Fin n) (w.adicCompletion E))
    (h : ∀ (e : ℕ) i k, Valued.v ((M e - 1) i k) ≤ WithZero.exp (-(e : ℤ))) :
    Filter.Tendsto M Filter.atTop (𝓝 1) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun k => ?_
  exact tendsto_of_v_le w _ _ fun e => h e i k

theorem UpperTheory.Gal.Int.Geo.Pl.nearNbhd_holds :
    UpperTheory.Gal.Int.Geo.Pl.NearNbhd := by
  intro E _ _ n w O hO h1
  by_contra hcon
  push_neg at hcon
  choose e' he g hgK hN hgO using hcon
  have hv : ∀ (e : ℕ) i k, Valued.v (((g e).val - 1) i k) ≤ WithZero.exp (-(e : ℤ)) := by
    intro e i k
    refine (v_le_of_inId w (e' e) _ (hN e i k)).trans ?_
    rw [WithZero.exp_le_exp]
    have := he e
    omega
  have ha : Filter.Tendsto (fun e => (g e).val) Filter.atTop (𝓝 1) := tendsto_mat_of_v_le w _ hv
  have hb : Filter.Tendsto (fun e => ((g e)⁻¹).val) Filter.atTop (𝓝 1) :=
    tendsto_mat_of_v_le w _ fun e => v_inv_sub_one_le w (g e) (hgK e) _ (hv e)
  have ht : Filter.Tendsto g Filter.atTop (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    exact ha.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hb)
  obtain ⟨e, hE⟩ := (ht.eventually (hO.mem_nhds h1)).exists
  exact hgO e hE
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private def iT {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) : GL (Fin n) R :=
  ⟨(g⁻¹).valᵀ, g.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one], by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩

private theorem iT_one {R : Type} [CommRing R] {n : ℕ} : iT (1 : GL (Fin n) R) = 1 := Units.ext (by simp [iT])

private theorem iT_cont {R : Type} [CommRing R] [TopologicalSpace R] {n : ℕ} : Continuous (iT : GL (Fin n) R → GL (Fin n) R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

private theorem iT_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {w : Plc E} {g : GLw n w} (h : g ∈ KGL w (n := n)) : iT g ∈ KGL w (n := n) := by
  rw [GlobalTheory.HenQ.Basic.mem_KGL_iff] at h ⊢
  exact ⟨fun i j => h.2 j i, fun i j => h.1 j i⟩

private theorem kgl_open {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) : IsOpen (KGL w (n := n) : Set (GLw n w)) := by
  have h : IsOpen ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := Valued.isOpen_valuationSubring _
  have : (KGL w (n := n) : Set (GLw n w)) = (⋂ i, ⋂ j, (fun g : GLw n w => g.val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E))) ∩
      ⋂ i, ⋂ j, (fun g : GLw n w => (g⁻¹).val i j) ⁻¹' ((w.adicCompletionIntegers E : ValuationSubring _) : Set (w.adicCompletion E)) := by
    ext g
    simp only [SetLike.mem_coe, GlobalTheory.HenQ.Basic.mem_KGL_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_val.matrix_elem i j)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h.preimage (Units.continuous_coe_inv.matrix_elem i j))

private theorem comp_th {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (F : Frame S) (w : Plc E) (k : GUf E n) : comp w (F.th k) = iT (comp w k) := by
  refine Units.ext ?_
  have h1 : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
  show (mat (F.th k)).val.map (pLoc E w) = ((comp w k)⁻¹).valᵀ
  rw [F.th_mat, h1]
  rfl

theorem stabOf_of (hN : NearNbhd) (hP : PrimeProj) (hD : Dict) : StabOf := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hoff
  have hoff' : ∀ u ∈ V.S, (p : 𝓞 E) ∉ u.asIdeal := by first | exact hoff.1 | exact hoff
  have hcof := Filter.eventually_cofinite.1 F.a_cof
  have hc : ∀ u : Plc E, Continuous fun g : GLw n u => (F.a u)⁻¹ * g * F.a u := fun u =>
    (continuous_const.mul continuous_id).mul continuous_const
  have hO : ∀ u : Plc E, ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL u (n := n), Near1 u e' g →
      (F.a u)⁻¹ * g * F.a u ∈ KGL u (n := n) ∧ (u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u) := fun u => by
    refine hN E n u (((fun g : GLw n u => (F.a u)⁻¹ * g * F.a u) ⁻¹' (KGL u (n := n) : Set (GLw n u))) ∩
      {g | u ∈ V.S → iT ((F.a u)⁻¹ * g * F.a u) ∈ V.Kw u}) (((kgl_open u).preimage (hc u)).inter ?_) ⟨?_, fun _ => ?_⟩
    · by_cases hu : u ∈ V.S
      · simp only [hu, true_imp_iff]
        exact (V.shape.opn u hu).preimage (iT_cont.comp (hc u))
      · simp [hu]
    · simp [Subgroup.one_mem]
    · simp [iT_one, Subgroup.one_mem]
  choose e he using hO
  have hJ : IsOpen (V.J : Set (GLw n w₀)) := V.Kw0 ▸ V.shape.opn w₀ V.shape.mem
  obtain ⟨e₀, he₀⟩ := hN E n w₀ ((fun g : GLw n w₀ => iT ((F.a w₀)⁻¹ * g * F.a w₀)) ⁻¹' (Subtype.val '' {k : V.J | V.χ k = 1}))
    ((hJ.isOpenMap_subtype_val _ V.ker_open).preimage (iT_cont.comp (hc w₀))) ⟨1, map_one _, by simp [iT_one]⟩
  have hT : ∀ u ∈ V.S ∪ hcof.toFinset, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u (n := n)) := fun u hu => by
    rw [Finset.mem_union, Set.Finite.mem_toFinset] at hu
    exact ⟨hu.elim (hoff' u) fun h h' => h (F.a_int u p hp.out S.good h'), hu⟩
  refine ⟨V.S ∪ hcof.toFinset, (V.S ∪ hcof.toFinset).sup e + e₀, hT, fun k' hk hn => ?_⟩
  obtain ⟨π, hπ⟩ := hP E n p hp.out
  have hK := (hD E A n p S F k').2.1.1 hk
  have hj : F.j (k' * (π k')⁻¹) = F.j k' := by
    rw [map_mul, map_inv, (F.ker _).2 fun w hw => (hπ k' w).2 hw, inv_one, mul_one]
  have h1 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (k' * (π k')⁻¹) = 1 := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).1 hw, mul_inv_cancel]
  have h2 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      comp w (k' * (π k')⁻¹) = (F.a w)⁻¹ * (F.a w * comp w k' * (F.a w)⁻¹) * F.a w := fun w hw => by
    rw [map_mul, map_inv, (hπ k' w).2 hw]; group
  have h3 := fun u hu => he u _ ((Finset.le_sup (f := e) hu).trans (Nat.le_add_right _ e₀)) _ (hK u (hT u hu).1) (hn u hu)
  have h4 : ∀ w : Plc E, comp w (F.th (k' * (π k')⁻¹)) ∈ KGL w (n := n) := fun w => by
    rw [comp_th]
    refine iT_mem ?_
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [h1 w hw]; exact Subgroup.one_mem _
    rw [h2 w hw]
    by_cases hu : w ∈ V.S ∪ hcof.toFinset
    · exact (h3 w hu).1
    · rw [Finset.mem_union, Set.Finite.mem_toFinset, not_or, Set.mem_setOf_eq, not_not] at hu
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu.2) (hK w hw)) hu.2
  have hw₀ : w₀ ∈ V.S ∪ hcof.toFinset := Finset.mem_union_left _ V.shape.mem
  obtain ⟨y, hy, hy'⟩ := he₀ _ (Nat.le_add_left _ _) _ (hK w₀ (hT w₀ hw₀).1) (hn w₀ hw₀)
  have h5 : comp w₀ (F.th (k' * (π k')⁻¹)) = y := by rw [comp_th, h2 w₀ (hT w₀ hw₀).1, hy']
  refine ⟨_, hj, CertificateRingHomMap.mem_lev.2 ⟨CertificateRingHomMap.pIntSim_of E n S.facts.pos _ h4, fun w hw => ?_, fun w _ _ => h4 w⟩, h5 ▸ y.2, ?_⟩
  · have hu := Finset.mem_union_left hcof.toFinset hw
    rw [comp_th, h2 w (hT w hu).1]
    exact (h3 w hu).2 hw
  · rw [← hy]
    exact congrArg _ (Subtype.ext h5)

end UpperTheory.Gal.Int.Geo.Pl
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp rat mat)

namespace UpperTheory.Gal.W2.Seed

theorem isoEx'_holds : IsoEx' := fun E _ _ _ A n hn => by
  obtain ⟨a, h1, h2⟩ := UpperTheory.Gal.G1.IsoEx_holds E A n hn
  refine ⟨a, ?_, h2⟩
  rw [Matrix.diagonal_map (map_zero _)] at h1
  exact h1

theorem adTEx_holds : AdTEx := pAdTEx pAdQEx pAdTensor pIdemP

theorem trEx_holds : TrEx := pTrEx adTEx_holds pMuEx isoEx'_holds (pJEx pMuStar) pJEq (pJSurj pIdemP pMuStar)

theorem latCoord_holds : LatCoord := pLatCoord pRepLaws

theorem vecCoord_holds : VecCoord := pVecCoord latCoord_holds pEvEx

end UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.W2.Seed

theorem intCof_holds : UpperTheory.Gal.Int.Geo.Pl.IntCof := fun E _ _ _ n g => pIntCof E n (mat g)

theorem frameEx_holds : FrameEx := fun E _ _ _ A n p _ S hn => by
  obtain ⟨T⟩ := trEx_holds E A n p S hn
  obtain ⟨vec, v1, v2, v3, v4, v5, v6⟩ := vecCoord_holds E A n p S T
  obtain ⟨B, x, hx, hm, he⟩ := pStdForm2 pMuStar E A n p S T
  exact ⟨{
    j := T.j
    surj := fun h => ⟨T.sec h, T.j_sec h⟩
    ker := fun g => by simpa using T.j_eq g 1
    a := fun w => GeneralLinearGroup.map (pLoc E w) T.a
    a_int := T.iso.2
    a_cof := pIntCof E n T.a
    vec := vec
    vec_inj := v1
    vec_hat := v2
    vec_surj := v3
    vec_in := v4
    vec_act := v5
    vec_mul := v6
    ρ := T.ρ
    ρ_int := T.int
    mult := T.j_sim
    B := B
    x := x
    t := 1
    hx := hx
    mem := hm
    emb1 := he
    emb2 := fun y _ h' => ⟨fun h => (pPInt E A n p S ⟨y, h'⟩ h).1, fun h => pPIntRev pIntConj E A n p S ⟨y, h'⟩ h⟩
    th := CertificateRingHomMap.th
    th_mat := fun _ => rfl
    th_sim := fun _ => rfl
    tr := T
    j_tr := rfl
    a_tr := fun _ => rfl }⟩

end UpperTheory.Gal.Int.Geo.Pl
end
end
