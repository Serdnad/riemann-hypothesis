module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle764
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle408
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.RedO

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (k : ℕ) (e0 : Fin d ⊕ Fin k → MvPowerSeries (Fin d) C) (lb : Module.Basis (Fin k) O G.dual.Lie), IsBasis c.μ e0 → IsAdapted (RingHom.id O) c.μ e0 → (∀ j, c.IsLie (e0 (Sum.inr j)) (lb j)) → ∀ h : MvPowerSeries (Fin d) C, QL c.μ ⊤ h → cob1 (up C c.μ) h = 0 → ∀ a : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (h - comb a e0) → (∀ j, a (Sum.inr j) = 0) ∧ ∀ i, lin h i = algebraMap O C (a (Sum.inl i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c k e0 lb hB hA hL h hh hcob a ha
  have hF : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hμ : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, c.isLaw.const i]

  have lie0 : ∀ f : MvPowerSeries (Fin d) C, cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
    intro f hf
    have hd : ∀ n : ℕ, defect c.μ (p ^ n) f = defect c.μ (p ^ n) (0 : MvPowerSeries (Fin d) C) := fun n => by
      rw [defect, GlobalTheory.LieZero.subst_nmul_of_cob1_eq_zero c.μ c.isLaw.const f hf, sub_self, defect,
        ← coe_substAlgHom (hasSubst_up_nmul c.isLaw.const _), map_zero, smul_zero, sub_zero]
    have e : c.IsLie f 0 ↔ c.IsLie (0 : MvPowerSeries (Fin d) C) 0 := by
      unfold Chart.IsLie
      simp only [hd]
    exact e.2 (c.isLie_zero hv.hom_inj)

  have hcobE : ∀ i, cob1 (up C c.μ) (e0 (Sum.inl i)) = 0 := fun i => by
    ext α
    obtain ⟨b, hb, hb'⟩ := (hA i).1 α
    rw [RingHom.mem_ker, RingHom.id_apply] at hb
    rw [hb', hb, map_zero, map_zero]
  let L : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) lb
  have hLe : ∀ x, c.IsLie (e0 x) (L x) := by
    rintro (i | j)
    · exact lie0 _ (hcobE i)
    · exact hL j

  let e' : Unit ⊕ (Fin d ⊕ Fin k) → MvPowerSeries (Fin d) C := Sum.elim (fun _ => h) e0
  let b' : Unit ⊕ (Fin d ⊕ Fin k) → O := Sum.elim (fun _ => 1) (-a)
  have hcomb : comb b' e' = h - comb a e0 := by
    simp only [comb, Fintype.sum_sum_type, e', b', Sum.elim_inl, Sum.elim_inr, Pi.neg_apply,
      map_neg, neg_smul, Finset.sum_neg_distrib, map_one, one_smul, Finset.univ_unique,
      Finset.sum_singleton]
    abel
  have hQL : ∀ x, QL c.μ ⊤ (e' x) := by
    rintro (_ | x)
    · exact hh
    · exact hB.1 x
  have hLie' : ∀ x, c.IsLie (e' x) (Sum.elim (fun _ => (0 : G.dual.Lie)) L x) := by
    rintro (_ | x)
    · exact lie0 h hcob
    · exact hLe x
  have hs := GlobalTheory.QLog.Chart.isLie_comb p O C hF G d c _ e' _ b' hQL hLie'
  rw [hcomb] at hs
  have hc0 : constantCoeff (h - comb a e0) = 0 := by

    rw [map_sub, hh.1, comb, map_sum]
    simp [← coeff_zero_eq_constantCoeff_apply, coeff_smul,
      coeff_zero_eq_constantCoeff_apply, (hB.1 _).1]
  have hl0 := (GlobalTheory.LieZero.lie_eq_zero p O C hF G d c _ _ hs).1 ha hc0
  simp only [Fintype.sum_sum_type, b', Sum.elim_inl, Sum.elim_inr, smul_zero, Finset.sum_const_zero,
    zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, neg_eq_zero, L] at hl0
  have hinr : ∀ j, a (Sum.inr j) = 0 :=
    Fintype.linearIndependent_iff.1 lb.linearIndependent (fun j => a (Sum.inr j)) hl0
  refine ⟨hinr, fun i => ?_⟩

  have hcobc : cob1 (up C c.μ) (h - comb a e0) = 0 := by
    have hadd : ∀ f g, cob1 (up C c.μ) (f + g) = cob1 (up C c.μ) f + cob1 (up C c.μ) g :=
      formalCoboundary_add hμ
    let Φ : MvPowerSeries (Fin d) C →+ MvPowerSeries (Fin d ⊕ Fin d) C :=
      AddMonoidHom.mk' (cob1 (up C c.μ)) hadd
    have e1 : cob1 (up C c.μ) (comb a e0) = 0 := by
      change Φ (comb a e0) = 0

      rw [comb, map_sum]
      refine Finset.sum_eq_zero fun x _ => ?_
      change cob1 (up C c.μ) (algebraMap O C (a x) • e0 x) = 0
      rw [formalCoboundary_smul hμ]
      rcases x with i' | j
      · rw [hcobE i', smul_zero]
      · rw [hinr j, map_zero, zero_smul]
    rw [sub_eq_add_neg, ← neg_one_smul C (comb a e0), hadd, formalCoboundary_smul hμ, e1, smul_zero, hcob,
      add_zero]
  obtain ⟨s, hs'⟩ := In.top_iff.1 ha
  have hs0 : s = 0 :=
    GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero p C v O hv G d c C hF s (by rw [hs']; exact hcobc)
  rw [hs0, map_zero] at hs'
  have hEq : h = comb a e0 := sub_eq_zero.1 hs'.symm
  rw [hEq]

  simp only [lin, comb, Fintype.sum_sum_type, map_add (f := _), map_sum, coeff_smul, smul_eq_mul]
  have h2 : ∀ j, algebraMap O C (a (Sum.inr j)) * coeff (Finsupp.single i 1) (e0 (Sum.inr j)) = 0 :=
    fun j => by rw [hinr j, map_zero, zero_mul]
  have h1 : ∀ i', coeff (Finsupp.single i 1) (e0 (Sum.inl i')) = (Pi.single i' (1 : C) : Fin d → C) i :=
    fun i' => congrFun (hA i').2 i
  simp only [h2, h1, Finset.sum_const_zero, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.QLog.RedO
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEtale

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_lift_neg {R : Type} [CommRing R] {K M N : _root_.GlobalTheory.EtC.Cx R} (a : K ⟶ M) (b : K ⟶ N) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (x : CohomologyClass (M ⊞ N) I n) :
    _root_.GlobalTheory.EtC.cpull (biprod.lift a (-b)) I n x =
      _root_.GlobalTheory.EtC.cpull a I n (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n x) - _root_.GlobalTheory.EtC.cpull b I n (_root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n x) := by
  rw [biprod.lift_eq, _root_.GlobalTheory.EtC.BiprodCls.cpull_add, Preadditive.neg_comp,
    _root_.GlobalTheory.EtC.MayerVietoris.cpull_neg, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull,
    _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.cpull_desc_pair {R : Type} [CommRing R] {M N L : _root_.GlobalTheory.EtC.Cx R} (c : M ⟶ L) (d : N ⟶ L) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ)
    (z : CohomologyClass L I n) :
    (_root_.GlobalTheory.EtC.cpull (biprod.inl : M ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z),
      _root_.GlobalTheory.EtC.cpull (biprod.inr : N ⟶ M ⊞ N) I n (_root_.GlobalTheory.EtC.cpull (biprod.desc c d) I n z)) = (_root_.GlobalTheory.EtC.cpull c I n z, _root_.GlobalTheory.EtC.cpull d I n z) := by
  rw [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_desc,
    biprod.inr_desc]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
open scoped TensorProduct in
theorem _root_.GlobalTheory.EtC.MVEtale.chains_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A)
    (h1 : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (h2 : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) :
    ∃ w, (ShortComplex.mk (biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)))) ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))) w).ShortExact := by
  have hcomp : (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
    IsLocalization.map_comp _
  have hsq : _root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f)) =
      _root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))) ≫
      _root_.GlobalTheory.EtC.spMap (algebraMap A A') := by
    unfold _root_.GlobalTheory.EtC.spMap
    rw [← Functor.map_comp, ← Functor.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp]
  have hchains := ((_root_.GlobalTheory.EtC.chains R).map_comp _ _).symm.trans
    ((congrArg (_root_.GlobalTheory.EtC.chains R).map hsq).trans
      ((_root_.GlobalTheory.EtC.chains R).map_comp _ _))
  obtain ⟨w', hw'⟩ := _root_.GlobalTheory.EtC.MVExact.mv_exact R A A' f h1 h2
  have hfree := _root_.GlobalTheory.EtC.MVFree.shortExact R A A' f ⟨h1, h2⟩ w'
  have w : biprod.lift ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (-(_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ≫
      biprod.desc ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
        ((_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A'))) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, hchains, add_neg_cancel]
  refine ⟨w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_⟩
  rcases lt_or_ge 0 i with hi | hi
  · have hX₁ := _root_.GlobalTheory.EtC.chains_isZero_pos R
      (_root_.GlobalTheory.EtC.sp (Localization.Away (algebraMap A A' f))) i hi
    have hX₃ := _root_.GlobalTheory.EtC.chains_isZero_pos R (_root_.GlobalTheory.EtC.sp A) i hi
    have hX₂ : IsZero (((_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp (Localization.Away f)) ⊞
        (_root_.GlobalTheory.EtC.chains R).obj (_root_.GlobalTheory.EtC.sp A')).X i) :=
      IsZero.of_iso ((biprod_isZero_iff _ _).2
        ⟨_root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi, _root_.GlobalTheory.EtC.chains_isZero_pos R _ i hi⟩)
        (HomologicalComplex.biprodXIso _ _ i)
    exact
      { exact := ShortComplex.exact_of_isZero_X₂ _ hX₂
        mono_f := ⟨fun _ _ _ => hX₁.eq_of_tgt _ _⟩
        epi_g := ⟨fun _ _ _ => hX₃.eq_of_src _ _⟩ }
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    exact _root_.GlobalTheory.EtC.mv_map_shortExact (HomologicalComplex.eval _ _ (-(p : ℤ)))
      (a := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (Localization.awayMap (algebraMap A A') f)))
      (b := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))))
      (f := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A (Localization.Away f))))
      (g := (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.spMap (algebraMap A A')))
      (W' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away ((algebraMap A A') f))))))
      (X' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of (Localization.Away f)))))
      (Y' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A'))))
      (Z' := (_root_.GlobalTheory.EtC.free R).obj (yoneda.obj (Spec (CommRingCat.of A))))
      (a' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f)))))
      (b' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))
      (f' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      (g' := (_root_.GlobalTheory.EtC.free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso R _ p) (_root_.GlobalTheory.EtC.chainsXIso R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p)
      (_root_.GlobalTheory.EtC.chainsXIso_naturality R _ p) w w' hfree

end GlobalTheory.EtC.MVEtale
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.tateTwistUnitClass_rootClass_spec : ∀ (q : ℕ) [NeZero q], (∀ E : Spc, Inv q E → ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk α = one q E ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) ∧ (∀ E : Spc, Inv q E → ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, (∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ) → CohomologyClass.mk α = one q E) ∧ (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → pull _ f _ _ (one q E') = one q E) ∧ ∀ (i : ℤ) (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)), rootClass i ζ = secClass (tw q i) (twGen i ζ) := by
  first | (exact @GlobalTheory.EtC.one_root_spec) | (exact GlobalTheory.EtC.one_root_spec) | (intros; apply GlobalTheory.EtC.one_root_spec  <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzMult

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (d : ℕ) (σ p : ℂ), d.Prime → 4 < d → l ≠ d → Sz l lam 0 (12 * p) → Sz l lam 0 (-2 * (d : ℂ) * σ + ((d : ℂ) + 1) * p) → (l = 3 → d % 3 = 2) → Sz l lam (if l = 2 then (if d % 4 = 3 then 1 else 2) else 0) σ := by
  intro l _ lam d σ p hd hd4 hld hA hB h3
  have hlp : l.Prime := Fact.out
  obtain ⟨hint, -, hmul, hmono, -, hl, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  obtain ⟨-, hadd2, -, -, hZ, -⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hne : ∀ n : ℕ, ¬ l ∣ n → (n : ℂ) ≠ 0 := by
    intro n hn h
    apply hn
    rw [Nat.cast_eq_zero.mp h]
    exact dvd_zero l
  have hinv : ∀ n : ℕ, ¬ l ∣ n → Sz l lam 0 ((n : ℂ)⁻¹) := by
    intro n hn
    apply hint n _ hn
    rw [mul_inv_cancel₀ (hne n hn)]
    exact isIntegral_one
  have hnat : ∀ n : ℕ, Sz l lam 0 (n : ℂ) := fun n => by exact_mod_cast hZ n
  have hm0 : ∀ (r : ℝ) (x y : ℂ), Sz l lam 0 x → Sz l lam r y → Sz l lam r (x * y) := by
    intro r x y hx hy
    simpa using hmul 0 r x y hx hy
  have hcancel : ∀ (r : ℝ) (n : ℕ) (x : ℂ), ¬ l ∣ n → Sz l lam r ((n : ℂ) * x) → Sz l lam r x := by
    intro r n x hn h
    have := hm0 r _ _ (hinv n hn) h
    rwa [← mul_assoc, inv_mul_cancel₀ (hne n hn), one_mul] at this
  have hkey : ∀ r : ℝ, 0 ≤ r → Sz l lam r (((d : ℂ) + 1) * p) → Sz l lam r (((2 * d : ℕ) : ℂ) * σ) := by
    intro r hr h
    have hB' := hmono 0 r _ hr hB
    have := (hadd2 r _ _ h hB').2
    convert this using 1
    push_cast
    ring
  have hmulk : ∀ (r : ℝ) (m k : ℕ), d + 1 = m * k → Sz l lam r ((m : ℂ) * p) → Sz l lam r (((d : ℂ) + 1) * p) := by
    intro r m k hk h
    have := hm0 r (k : ℂ) _ (hnat k) h
    have e : ((d : ℂ) + 1) = (m : ℂ) * k := by exact_mod_cast hk
    rw [e]
    convert this using 1
    ring
  by_cases h2 : l = 2
  · subst h2
    have hd2 : ¬ 2 ∣ d := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h
      omega
    have h4p : Sz 2 lam 0 (((4 : ℕ) : ℂ) * p) := by
      apply hcancel 0 3 _ (by norm_num)
      convert hA using 1
      push_cast
      ring
    rw [if_pos rfl]
    split_ifs with h43
    · obtain ⟨k, hk⟩ : 4 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 4 k hk h4p)
      have h2s : Sz 2 lam 0 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 0 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 0 σ).mp h2s
      norm_num at this
      exact this
    · have h2p : Sz 2 lam 1 (((2 : ℕ) : ℂ) * p) := by
        have := (hl 0 (((2 : ℕ) : ℂ) * p)).mp (by convert h4p using 1; push_cast; ring)
        norm_num at this ⊢
        exact this
      obtain ⟨k, hk⟩ : 2 ∣ d + 1 := by omega
      have h1 := hkey 1 zero_le_one (hmulk 1 2 k hk h2p)
      have h2s : Sz 2 lam 1 (((2 : ℕ) : ℂ) * σ) := by
        apply hcancel 1 d _ hd2
        convert h1 using 1
        push_cast
        ring
      have := (hl 1 σ).mp h2s
      norm_num at this
      exact this
  · rw [if_neg h2]
    by_cases h3' : l = 3
    · subst h3'
      have hd3 := h3 rfl
      have h3p : Sz 3 lam 0 (((3 : ℕ) : ℂ) * p) := by
        apply hcancel 0 4 _ (by norm_num)
        convert hA using 1
        push_cast
        ring
      obtain ⟨k, hk⟩ : 3 ∣ d + 1 := by omega
      have h1 := hkey 0 le_rfl (hmulk 0 3 k hk h3p)
      exact hcancel 0 (2 * d) σ (by omega) h1
    · have hl2 : ∀ n : ℕ, n.Prime → l ∣ n → l = n := fun n hn h =>
        (Nat.prime_dvd_prime_iff_eq hlp hn).mp h
      have h12 : ¬ l ∣ 12 := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp (show l ∣ 2 * 2 * 3 from h) with h' | h'
        · rcases (Nat.Prime.dvd_mul hlp).mp h' with h'' | h'' <;>
            exact h2 (hl2 2 Nat.prime_two h'')
        · exact h3' (hl2 3 Nat.prime_three h')
      have h2d : ¬ l ∣ 2 * d := by
        intro h
        rcases (Nat.Prime.dvd_mul hlp).mp h with h' | h'
        · exact h2 (hl2 2 Nat.prime_two h')
        · exact hld (hl2 d hd h')
      have hp : Sz l lam 0 p := by
        apply hcancel 0 12 p h12
        exact_mod_cast hA
      have h1 := hkey 0 le_rfl (hmulk 0 1 (d + 1) (by ring) (by simpa using hp))
      exact hcancel 0 (2 * d) σ h2d h1

end GlobalTheory.SzMult
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.ArithThreeInert

theorem main : ∀ [Fact (Nat.Prime 3)] (lam : algebraicClosure ℚ ℂ →+* ℂ_[3]) (d : ℕ) (w σ p : ℂ), d % 3 = 1 → w ^ 2 = -(d : ℂ) → Sz 3 lam 0 (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz 3 lam 0 (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p) → Sz 3 lam 0 σ := by
  intro _ lam d w σ p hd hw h1 h2
  obtain ⟨hint, hadd, hmul, -, hneg, -, -⟩ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties 3 lam
  have hsub : ∀ x y : ℂ, Sz 3 lam 0 x → Sz 3 lam 0 y → Sz 3 lam 0 (x - y) := by
    intro x y hx hy
    rw [sub_eq_add_neg]; exact hadd 0 x (-y) hx (hneg 0 y hy)
  have hI : ∀ x : ℂ, IsIntegral ℤ x → Sz 3 lam 0 x := by
    intro x hx
    exact hint 1 x (by norm_num) (by simpa using hx)
  have hw_int : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.Monic.def.mpr (by
        rw [Polynomial.leadingCoeff_X_pow_add_C (by norm_num)])
    · simp [hw]
  have hA : Sz 3 lam 0 ((1 + w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.add hw_int).pow 2).sub isIntegral_one)
  have hB : Sz 3 lam 0 ((1 - w) ^ 2 - 1) :=
    hI _ (((isIntegral_one.sub hw_int).pow 2).sub isIntegral_one)
  have hW : Sz 3 lam 0 w := hI _ hw_int
  have hcomb : Sz 3 lam 0 (((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w) := by
    have := hmul 0 0 _ _ (hsub _ _ (by simpa using hmul 0 0 _ _ hB h1) (by simpa using hmul 0 0 _ _ hA h2)) hW
    simpa using this
  have heq : ((((1 - w) ^ 2 - 1) *
      (((1 + w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p)) -
      (((1 + w) ^ 2 - 1) * (((1 - w) ^ 2 - (1 + (d : ℂ))) * σ - ((1 - w) ^ 2 - 1) * p))) * w
      = ((4 * d ^ 2 : ℕ) : ℂ) * (-σ) := by
    push_cast
    linear_combination (4 * (d : ℂ) * σ) * hw
  rw [heq] at hcomb
  have hd0 : ((4 * d ^ 2 : ℕ) : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hd
    exact_mod_cast (by positivity : 0 < 4 * d ^ 2).ne'
  have h3 : ¬ 3 ∣ 4 * d ^ 2 := by
    intro h
    have h0 : (4 * d ^ 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.mul_mod, Nat.pow_mod, hd] at h0
    norm_num at h0
  have hinv : Sz 3 lam 0 (((4 * d ^ 2 : ℕ) : ℂ))⁻¹ :=
    hint (4 * d ^ 2) _ h3 (by rw [mul_inv_cancel₀ hd0]; exact isIntegral_one)
  have hm := hmul 0 0 _ _ hinv hcomb
  rw [zero_add] at hm
  have hfin := hneg 0 _ hm
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul, neg_neg] at hfin
  exact hfin

end GlobalTheory.ArithThreeInert
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  first | exact @GlobalTheory.ConjCoordToric.conj_coordIn_toric | exact GlobalTheory.ConjCoordToric.conj_coordIn_toric | (intros; apply GlobalTheory.ConjCoordToric.conj_coordIn_toric <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.FockAdjLines
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem inner_omAct_adj : ∀ (p q r s : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : Pol p q r s →ₗ[ℂ] H), IsFockIP ι → ∀ (Z : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P Q : Pol p q r s), inner ℂ (ι (omAct p q r s Z P)) (ι Q) = inner ℂ (ι P) (ι (omAct p q r s (Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s) * Z.conjTranspose * Matrix.kroneckerMap (· * ·) (Jm p q) (Jm r s)) Q)) := by
  intro p q r s H _ _ ι hι Z P Q
  refine GlobalTheory.FockAdj.inner_omAct hι _ _ ?_ P Q
  rintro ⟨a, c⟩ ⟨b, d⟩
  rw [Jm_eq_diagonal, Jm_eq_diagonal, Matrix.kroneckerMap_diagonal_diagonal _ (by simp) (by simp),
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    simp [linePos]

end GlobalTheory.FockAdjLines
end
end

section

open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

theorem _root_.GlobalTheory.T.exists_cechOneCocycle_on_affine_cover_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ i, V i = ⊤ → (∀ k, IsAffineOpen (U k)) → ∀ z : C1 V, IsCoc V z → ∃ (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), IsCoc U z' ∧ (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) ∧ ∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k') := by
  first | exact @GlobalTheory.CechMixed.exists_cocycle_on_affine | exact GlobalTheory.CechMixed.exists_cocycle_on_affine | (intros; apply GlobalTheory.CechMixed.exists_cocycle_on_affine <;> assumption)
end
