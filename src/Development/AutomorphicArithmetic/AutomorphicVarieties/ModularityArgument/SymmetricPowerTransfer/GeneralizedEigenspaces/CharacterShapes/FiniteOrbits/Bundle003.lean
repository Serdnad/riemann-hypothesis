module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle001
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Box

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K U : ∀ v, Subgroup (Gv v)}

private theorem memBox (P : RPG G Gv K) (U : ∀ v, Subgroup (Gv v)) (g : G) :
    g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

private theorem smulMk {A : Type} [Group A] (W W' : Subgroup A) (u : W) (x : A) :
    u • (x : A ⧸ W') = (((u : A) * x : A) : A ⧸ W') := rfl

end Box

end UpperTheory.V.Z.Sym.So

private theorem mem_doubleCoset_iff_exists_eq_mul_mul {A : Type} [Group A] {W : Subgroup A} {a x : A} :
    x ∈ DC W a ↔ ∃ u ∈ W, ∃ u' ∈ W, x = u * a * u' := Iff.rfl

private theorem mul_mem_doubleCoset_of_mem_doubleCoset_of_mem {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : x * c ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨u, hu, u' * c, mul_mem hu' hc, by simp only [mul_assoc]⟩

private theorem mul_mem_doubleCoset_of_mem_of_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a x c : A}
    (hx : x ∈ DC W a) (hc : c ∈ W) : c * x ∈ DC W a := by
  obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hx
  exact mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨c * u, mul_mem hc hu, u', hu', by simp only [mul_assoc]⟩

private theorem out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset {A : Type} [Group A] {W : Subgroup A} {a b g x : A}
    (h1 : x ∈ DC W a) (h2 : x⁻¹ * g ∈ DC W b) :
    Quotient.out (x : A ⧸ W) ∈ DC W a ∧ (Quotient.out (x : A ⧸ W))⁻¹ * g ∈ DC W b := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul W x
  rw [hc]
  refine ⟨mul_mem_doubleCoset_of_mem_doubleCoset_of_mem h1 c.2, ?_⟩
  rw [mul_inv_rev, mul_assoc]
  exact mul_mem_doubleCoset_of_mem_of_mem_doubleCoset h2 (inv_mem c.2)

private theorem quotientGroup_coe_out_eq_self {A : Type} [Group A] (W : Subgroup A) (y : A ⧸ W) :
    ((Quotient.out y : A) : A ⧸ W) = y := Quotient.out_eq y

theorem UpperTheory.V.Z.Sym.So.uFBox :
    UpperTheory.V.Z.Sym.So.UFBox := by
  intro I G _ Gv _ K U P S _ a ha
  classical
  have hB : ∀ g, g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := memBox P U
  have glue : ∀ x : (v : I) → Gv v, (∀ v ∉ S, x v = 1) → ∃ h : G, ∀ v, P.p v h = x v := by
    intro x hx
    apply P.surj
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset ?_)
    intro v hv
    by_contra hvS
    exact hv (by rw [hx v hvS]; exact one_mem _)
  have key : ∀ c : G, (∀ v ∉ S, P.p v c ∈ U v) → ∀ g : G, g ∈ DC (P.box U) c ↔
      (∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v c)) ∧ ∀ v ∉ S, P.p v g ∈ U v := by
    intro c hc g
    constructor
    · intro hg
      obtain ⟨u, hu, u', hu', rfl⟩ := mem_doubleCoset_iff_exists_eq_mul_mul.1 hg
      rw [hB] at hu hu'
      refine ⟨fun v _ => mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨P.p v u, hu v, P.p v u', hu' v, by rw [map_mul, map_mul]⟩, fun v hv => ?_⟩
      rw [map_mul, map_mul]
      exact mul_mem (mul_mem (hu v) (hc v hv)) (hu' v)
    · rintro ⟨h1, h2⟩
      have h1' : ∀ v ∈ S, ∃ u ∈ U v, ∃ u' ∈ U v, P.p v g = u * P.p v c * u' :=
        fun v hv => mem_doubleCoset_iff_exists_eq_mul_mul.1 (h1 v hv)
      choose! u hu u' hu' hg using h1'
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then u v else 1) (fun v hv => if_neg hv)
      refine mem_doubleCoset_iff_exists_eq_mul_mul.2 ⟨w, ?_, c⁻¹ * w⁻¹ * g, ?_, by group⟩
      · rw [hB]
        intro v
        rw [hw]
        split_ifs with hv
        exacts [hu v hv, one_mem _]
      · rw [hB]
        intro v
        rw [map_mul, map_mul, map_inv, map_inv, hw]
        split_ifs with hv
        · rw [hg v hv]
          have e : (P.p v c)⁻¹ * (u v)⁻¹ * (u v * P.p v c * u' v) = u' v := by group
          rw [e]
          exact hu' v hv
        · rw [inv_one, mul_one]
          exact mul_mem (inv_mem (hc v hv)) (h2 v hv)
  refine ⟨key a ha, ?_, ?_⟩
  · intro hf
    unfold UpperTheory.V.AlgebraTools.FinOrb at hf ⊢
    have hout : ∀ u : P.box U, ∀ v ∉ S,
        P.p v (Quotient.out (u • (a : G ⧸ P.box U))) ∈ U v := by
      intro u v hv
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      rw [smulMk, hc, map_mul, map_mul]
      exact mul_mem (mul_mem ((hB _).1 u.2 v) (ha v hv)) ((hB _).1 c.2 v)
    apply Set.Finite.of_finite_image
      (f := fun (y : G ⧸ P.box U) (v : S) => ((P.p v.1 (Quotient.out y) : Gv v.1) : Gv v.1 ⧸ U v.1))
    · refine (Set.Finite.pi (t := fun v : S =>
        MulAction.orbit (U v.1) ((P.p v.1 a : Gv v.1) : Gv v.1 ⧸ U v.1)) (fun v => hf v.1 v.2)).subset ?_
      rintro _ ⟨y, ⟨u, rfl⟩, rfl⟩
      rw [Set.mem_univ_pi]
      intro v
      refine ⟨⟨P.p v.1 u, (hB _).1 u.2 v.1⟩, ?_⟩
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (P.box U) ((u : G) * a)
      simp only [smulMk]
      rw [hc, QuotientGroup.eq]
      convert (hB _).1 c.2 v.1 using 1
      simp only [map_mul, Subgroup.coe_mk]
      group
    · rintro _ ⟨u1, rfl⟩ _ ⟨u2, rfl⟩ h12
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans ((QuotientGroup.eq.2 ?_).trans (quotientGroup_coe_out_eq_self _ _))
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      by_cases hv : v ∈ S
      · exact QuotientGroup.eq.1 (congrFun h12 ⟨v, hv⟩)
      · exact mul_mem (inv_mem (hout u1 v hv)) (hout u2 v hv)
  · intro b hb hloc g
    have hab : ∀ v ∉ S, P.p v (a * b) ∈ U v := fun v hv => by
      rw [map_mul]
      exact mul_mem (ha v hv) (hb v hv)
    constructor
    · intro hg
      obtain ⟨hgS, hgN⟩ := (key _ hab g).1 hg
      have hgl : ∀ v ∈ S, P.p v g ∈ DC (U v) (P.p v a * P.p v b) := fun v hv => by
        rw [← map_mul]
        exact hgS v hv
      have hl : ∀ v ∈ S, ∃ z, z ∈ DC (U v) (P.p v a) ∧ z⁻¹ * P.p v g ∈ DC (U v) (P.p v b) := by
        intro v hv
        obtain ⟨y, hy, -⟩ := (hloc v hv (P.p v g)).1 (hgl v hv)
        exact ⟨_, hy⟩
      choose! z hz1 hz2 using hl
      obtain ⟨w, hw⟩ := glue (fun v => if v ∈ S then z v else 1) (fun v hv => if_neg hv)
      have hw1 : w ∈ DC (P.box U) a := (key a ha w).2
        ⟨fun v hv => by rw [hw, if_pos hv]; exact hz1 v hv,
         fun v hv => by rw [hw, if_neg hv]; exact one_mem _⟩
      have hw2 : w⁻¹ * g ∈ DC (P.box U) b := (key b hb _).2
        ⟨fun v hv => by rw [map_mul, map_inv, hw, if_pos hv]; exact hz2 v hv,
         fun v hv => by rw [map_mul, map_inv, hw, if_neg hv, inv_one, one_mul]; exact hgN v hv⟩
      refine ⟨(w : G ⧸ P.box U), out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hw1 hw2, ?_⟩
      rintro y ⟨hy1, hy2⟩
      refine (quotientGroup_coe_out_eq_self _ _).symm.trans (QuotientGroup.eq.2 ?_)
      rw [hB]
      intro v
      rw [map_mul, map_inv]
      have ha1 := (key a ha _).1 hy1
      have hb1 := (key b hb _).1 hy2
      by_cases hv : v ∈ S
      · have hb2 := hb1.1 v hv
        rw [map_mul, map_inv] at hb2
        have hz2' := hz2 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz2'
        have hz1' := hz1 v hv
        rw [← if_pos (c := v ∈ S) (t := z v) (e := 1) hv, ← hw v] at hz1'
        have e := ((hloc v hv (P.p v g)).1 (hgl v hv)).unique
          (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset (ha1.1 v hv) hb2) (out_mem_doubleCoset_and_out_inv_mul_mem_doubleCoset hz1' hz2')
        exact QuotientGroup.eq.1 e
      · rw [hw, if_neg hv]
        exact mul_mem (inv_mem (ha1.2 v hv)) (one_mem _)
    · intro y hy1 hy2
      refine (key _ hab g).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have h2 := ((key b hb _).1 hy2).1 v hv
        rw [map_mul, map_inv] at h2
        rw [map_mul]
        exact (hloc v hv (P.p v g)).2 (P.p v y) (((key a ha y).1 hy1).1 v hv) h2
      · have h1 := ((key a ha y).1 hy1).2 v hv
        have h2 := ((key b hb _).1 hy2).2 v hv
        rw [map_mul, map_inv] at h2
        have h3 := mul_mem h1 h2
        rwa [mul_inv_cancel_left] at h3

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_cong {L : Type} [Field L] [NumberField L] [IsCMField L] (m : ℕ) (hm : 3 ≤ m) (δ : L)
    (hδ : δ * IsCMField.complexConj L δ = 1)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) δ - 1 = (m : w.adicCompletion L) * a) : δ = 1 := by
  have hm0 : (m : L) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hx : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((δ - 1) / m) ≤ 1 := by
    intro v
    obtain ⟨a, ha, e⟩ := h v
    have hma : (m : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (m : L) := by simp
    have hm0' : (m : v.adicCompletion L) ≠ 0 := by
      rw [hma]
      exact (map_ne_zero _).2 hm0
    have hxa : algebraMap L (v.adicCompletion L) ((δ - 1) / m) = a := by
      rw [map_div₀, map_sub, map_one, e, ← hma]
      field_simp
    have hval : Valued.v (algebraMap L (v.adicCompletion L) ((δ - 1) / m)) = v.valuation L ((δ - 1) / m) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [← hval, hxa]
    exact ha
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L _ hx
  by_contra hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    have : δ - 1 = 0 := by
      have := hy.symm
      rwa [div_eq_zero_iff, or_iff_left hm0] at this
    exact hne (sub_eq_zero.1 this)
  have hlt : ∀ z : InfinitePlace L, z ((y : 𝓞 L) : L) < 1 := by
    intro z
    have hyx : ((y : 𝓞 L) : L) = (δ - 1) / m := hy
    have hn : ‖z.embedding δ‖ = 1 := by
      have e1 : z.embedding δ * (starRingEnd ℂ) (z.embedding δ) = 1 := by
        rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, hδ, map_one]
      have e2 := congrArg norm e1
      rw [norm_mul, Complex.norm_conj, norm_one] at e2
      nlinarith [norm_nonneg (z.embedding δ)]
    rw [← InfinitePlace.norm_embedding_eq, hyx, map_div₀, map_sub, map_one, map_natCast, norm_div,
      Complex.norm_natCast]
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_one (by linarith)]
    have := norm_sub_le (z.embedding δ) 1
    rw [hn, norm_one] at this
    linarith
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace L) := inferInstance
  have := InfinitePlace.one_le_of_lt_one (w := w₀) hy0 (fun z _ => hlt z)
  linarith [hlt w₀]

private theorem det_cong {L : Type} [Field L] [NumberField L] [IsCMField L] {m : ℕ} {w : HeightOneSpectrum (𝓞 L)}
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (h : ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (M - 1) i j = (m : w.adicCompletion L) * a) :
    ∃ a ∈ w.adicCompletionIntegers L, M.det - 1 = (m : w.adicCompletion L) * a := by
  obtain ⟨a, ha, ea⟩ := h 0 0
  obtain ⟨b, hb, eb⟩ := h 0 1
  obtain ⟨c, hc, ec⟩ := h 1 0
  obtain ⟨d, hd, ed⟩ := h 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at ea eb ec ed
  have hmO : (m : w.adicCompletion L) ∈ w.adicCompletionIntegers L := natCast_mem _ m
  refine ⟨a + d + m * (a * d - b * c), add_mem (add_mem ha hd) (mul_mem hmO (sub_mem (mul_mem ha hd) (mul_mem hb hc))), ?_⟩
  have e0 : M 0 0 = 1 + m * a := by rw [← ea]; ring
  have e3 : M 1 1 = 1 + m * d := by rw [← ed]; ring
  rw [Matrix.det_fin_two, e0, e3, eb, ec]
  ring

theorem UpperTheory.V.Z.Sym.So.detRoot :
    UpperTheory.V.Z.Sym.So.DetRoot := by
  intro L _ _ _ m hm U hU f hf k hk hr u hu hfu
  obtain ⟨γ₀, hγ₀'⟩ := hr
  have hγ₀ : ratGL L 2 γ₀ = ((f * k : UA L 2) : GA L 2) := hγ₀'
  have hg : Formalism.UG.cT (conjAd L) ((f * k : UA L 2) : GA L 2).val * 1 * ((f * k : UA L 2) : GA L 2).val = 1 := (f * k).2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL L 2 γ₀).val = γ₀.val.map (algebraMap L (Ad L)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap L (Ad L)) (IsCMField.complexConj L).toRingEquiv.toRingHom (conjAd L)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  haveI hnt : Nontrivial (Ad L) := show Nontrivial (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) from inferInstance
  have hUL : Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val * γ₀.val = 1 := by
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply (algebraMap L (Ad L)).injective
    rw [this]
    split_ifs <;> simp
  have hδ : γ₀.val.det * IsCMField.complexConj L γ₀.val.det = 1 := by
    have := congrArg Matrix.det hUL
    rw [Matrix.det_mul, Matrix.det_one] at this
    have hc : (Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).det = IsCMField.complexConj L γ₀.val.det := by
      simp only [Formalism.UG.cT, Matrix.det_transpose]
      exact (RingHom.map_det (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).symm
    rw [hc] at this
    rw [mul_comm]
    exact this
  have hD : (f : GA L 2).val.det * (k : GA L 2).val.det = algebraMap L (Ad L) γ₀.val.det := by
    rw [RingHom.map_det]
    have h2 : (γ₀.val.map (algebraMap L (Ad L))) = ((f * k : UA L 2) : GA L 2).val := by rw [← hv, hγ₀]
    change _ = (γ₀.val.map (algebraMap L (Ad L))).det
    rw [h2, ← Matrix.det_mul]
    rfl
  have hkF : pFin L (k : GA L 2).val.det = 1 := by
    have hk' : Matrix.GeneralLinearGroup.map (pFin L) (k : GA L 2) = 1 := hk
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Af L) => g.val.det) hk'
    simpa using this
  have hfI : pInf L (f : GA L 2).val.det = 1 := by
    have hf' : Matrix.GeneralLinearGroup.map (pInf L) (f : GA L 2) = 1 := hf
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Cinf L) => g.val.det) hf'
    simpa using this
  have hdu : (f : GA L 2).val.det * (u : GA L 2).val.det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det ((f * u : UA L 2) : GA L 2) = 1 := hfu
    have := congrArg Units.val h1
    simpa using this
  have huv : (u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det = 1 := by
    rw [← Matrix.det_mul]
    have : (u : GA L 2).val * ((u⁻¹ : UA L 2) : GA L 2).val = 1 := by
      have := congrArg (fun x : UA L 2 => (x : GA L 2).val) (mul_inv_cancel u)
      simpa using this
    rw [this, Matrix.det_one]
  have hfv : (f : GA L 2).val.det = ((u⁻¹ : UA L 2) : GA L 2).val.det := by
    calc _ = (f : GA L 2).val.det * ((u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det) := by rw [huv, mul_one]
      _ = _ := by rw [← mul_assoc, hdu, one_mul]
  have hcong : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) γ₀.val.det - 1 = (m : w.adicCompletion L) * a := by
    intro w
    have hmem := ((hU (u⁻¹)).1 (U.inv_mem hu)).2 w
    obtain ⟨a, ha, e⟩ := det_cong (mL w (u⁻¹ : UA L 2)) hmem
    refine ⟨a, ha, ?_⟩
    rw [← e]
    have e1 : (mL w (u⁻¹ : UA L 2)).det = pLoc L w (pFin L ((u⁻¹ : UA L 2) : GA L 2).val.det) := by
      rw [← RingHom.comp_apply, RingHom.map_det]
      rfl
    have e2 : algebraMap L (w.adicCompletion L) γ₀.val.det = pLoc L w (pFin L (algebraMap L (Ad L) γ₀.val.det)) := rfl
    rw [e1, e2, ← hD, hfv, map_mul, hkF, mul_one]
  have h1 : γ₀.val.det = 1 := eq_one_of_cong m hm _ hδ hcong
  rw [h1, map_one] at hD
  have hfF : pFin L (f : GA L 2).val.det = 1 := by
    have := congrArg (pFin L) hD
    rwa [map_mul, hkF, mul_one, map_one] at this
  have hf1 : (f : GA L 2).val.det = 1 := by
    refine Prod.ext ?_ hfF
    apply (infEq L).symm.injective
    have e : (infEq L).symm ((1 : Ad L).1) = 1 := map_one _
    exact hfI.trans e.symm
  have hk1 : (k : GA L 2).val.det = 1 := by rwa [hf1, one_mul] at hD
  refine ⟨?_, ?_⟩
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hf1
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hk1

end
end

section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma mul_of_genEig {P M : Type} [CommSemigroup P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (u : P → Module.End ℂ M) (hu : ∀ p q, u (p * q) = u p * u q) (hc : ∀ p q, Commute (u p) (u q))
    (ψ : P → ℂ) (h : IsGenEig u ψ) (p q : P) : ψ (p * q) = ψ p * ψ q := by
  obtain ⟨v, hv0, hv⟩ := (Tf.eigVec P M u hc ψ).1 h
  have h1 := hv (p * q)
  rw [hu, Module.End.mul_apply, hv q, map_smul, hv p, smul_smul] at h1
  rw [mul_comm (ψ p)]
  exact (smul_left_injective ℂ hv0 h1).symm

theorem UpperTheory.V.Z.Sym.So.posSpec :
    UpperTheory.V.Z.Sym.So.PosSpec := by
  unfold UpperTheory.V.Z.Sym.So.PosSpec
  intro P N I J _ _ _ _ _ Mi _ _ _ u w hu hw X b β hβ a c ha htr χ hχ hex
  have hcu : ∀ j p q, Commute (u j p) (u j q) := fun j p q => by
    unfold Commute SemiconjBy
    rw [← hu, ← hu, mul_comm]
  have hcw : ∀ p q, Commute (w p) (w q) := fun p q => by
    unfold Commute SemiconjBy
    rw [← hw, ← hw, mul_comm]
  by_cases hN : ∃ v, v ≠ 0 ∧ ∀ p, w p v = χ p • v
  · exact Or.inr hN
  left
  choose XX dd hXX hdd htrj using fun j => Tf.trPos P (Mi j) (u j) (hcu j)
  obtain ⟨XN, dN, hXN, hdN, htrN⟩ := Tf.trPos P N w hcw
  obtain ⟨j0, v0, hv0, hv0'⟩ := hex
  have hχj0 : χ ∈ XX j0 :=
    (hXX j0 χ).2 ((Tf.eigVec P (Mi j0) (u j0) (hcu j0) χ).2 ⟨v0, hv0, hv0'⟩)
  have hχN : χ ∉ XN := fun h => hN ((Tf.eigVec P N w hcw χ).1 ((hXN χ).1 h))
  let T : Option J → Finset (P → ℂ) := fun o => Option.elim o XN XX
  let S' : Finset (Σ _ : Option J, P → ℂ) := Finset.univ.sigma T
  let b' : (Σ _ : Option J, P → ℂ) → ℂ := fun k =>
    Option.elim k.1 ((c : ℂ) * (dN k.2 : ℂ)) (fun j => (a : ℂ) * (dd j k.2 : ℂ))
  let β' : (Σ _ : Option J, P → ℂ) → P → ℂ := fun k => k.2
  refine Tf.extract P I (Σ _ : Option J, P → ℂ) X S' b b' β β' hβ ?_ ?_ χ hχ ?_
  · rintro ⟨o, ψ⟩ hk p q
    simp only [S', Finset.mem_sigma, Finset.mem_univ, true_and] at hk
    cases o with
    | none => exact mul_of_genEig w hw hcw ψ ((hXN ψ).1 hk) p q
    | some j => exact mul_of_genEig (u j) (hu j) (hcu j) ψ ((hXX j ψ).1 hk) p q
  · intro p
    rw [htr p, htrN p]
    simp only [htrj, S', Finset.sum_sigma, Fintype.sum_option, T, b', β', Option.elim,
      Finset.mul_sum, mul_assoc]
    exact add_comm _ _
  · open ComplexOrder in
    · refine (Finset.sum_pos ?_ ⟨⟨some j0, χ⟩, ?_⟩).ne'
      · rintro ⟨o, ψ⟩ hk
        simp only [S', β', Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hk
        obtain ⟨hk1, rfl⟩ := hk
        cases o with
        | none => exact absurd hk1 hχN
        | some j =>
          simp only [b', Option.elim]
          exact mul_pos (Complex.zero_lt_real.2 ha) (by exact_mod_cast hdd j ψ hk1)
      · simp [S', β', T, hχj0]

end
end
