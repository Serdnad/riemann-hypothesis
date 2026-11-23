module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1752
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
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
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormInert

open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cT_aeval {K : Type} [Field K] (s : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (f : K[X]) :
    cT s (aeval A f) = aeval (cT s A) (f.map s) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext i j; simp [cT]
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map s)ᵀ ^ k = ((A ^ k).map s)ᵀ := by rw [← Matrix.transpose_pow, Matrix.map_pow]
    ext i j
    simp [cT, e, Algebra.algebraMap_eq_smul_one]

theorem exists_over (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ w : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v := by
  have := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  refine ⟨⟨P, hP.isPrime, fun h0 => v.ne_bot ?_⟩, HeightOneSpectrum.ext hPv.over.symm⟩
  rw [hPv.over, h0]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem localEquiv (hU : Unr E) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (w : Pl E)
    (hw : w.under (𝓞 (maximalRealSubfield E)) = v)
    (huniq : ∀ u : Pl E, u.under (𝓞 (maximalRealSubfield E)) = v → u = w) :
    ∃ j : w.adicCompletion E ≃+* v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E,
      (∀ e : E, j (algebraMap E _ e) = 1 ⊗ₜ e) ∧
      ∀ x, j (cj w x) = Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) (j x) := by
  classical
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u (hu.trans hw))
  have hmain := GlobalTheory.ConjAtPlace.main E hU w
  have hσ := (hmain.2.2.2.1 hns).1
  have hinj : Function.Injective (GlobalTheory.LFun.toCompl hw) := by
    refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
    have h1 := GlobalTheory.AutFunCompare.map_tensNU_self _ _ (GlobalTheory.AdelicU.singleFin_mul v)
      (GlobalTheory.AdelicU.evalV_singleFin_self v) y
    have h2 : GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E
        (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU _ (GlobalTheory.AdelicU.singleFin_mul v) y) = 0 :=
      FiniteAdeleRing.ext _ fun u => by
        by_cases e : u.under (𝓞 (maximalRealSubfield E)) = v
        · rw [GlobalTheory.LFun.finAdEquiv_apply e, h1]
          obtain rfl := huniq u e
          exact hy
        · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _
            (GlobalTheory.AdelicU.evalV_singleFin_ne e), map_zero]
          rfl
    rw [← h1, (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv (maximalRealSubfield E) E).injective).1 h2, map_zero]
  have hsurj := GlobalTheory.LFun.InertChart.toCompl_surjective hw
  let e := RingEquiv.ofBijective (GlobalTheory.LFun.toCompl hw) ⟨hinj, hsurj⟩
  have hF : ∀ a, cj w (GlobalTheory.LFun.complMap hw a) = GlobalTheory.LFun.complMap hw a := by
    have := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      (hmain.1.comp (GlobalTheory.LFun.InertChart.continuous_complMap hw)) (GlobalTheory.LFun.InertChart.continuous_complMap hw)
      (funext fun x => by
        simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))
    exact fun a => congrFun this a
  have hcomp : ∀ y, cj w (GlobalTheory.LFun.toCompl hw y) = GlobalTheory.LFun.toCompl hw
      (Algebra.TensorProduct.map (AlgHom.id (maximalRealSubfield E) (v.adicCompletion (maximalRealSubfield E)))
        ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →ₐ[maximalRealSubfield E] E) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [GlobalTheory.LFun.toCompl_tmul, hF, hσ]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  refine ⟨e.symm, fun x => e.symm_apply_eq.2 ?_, fun x => e.symm_apply_eq.2 ?_⟩
  · have h := GlobalTheory.LFun.toCompl_tmul hw 1 x
    rw [map_one, one_mul] at h
    exact h.symm
  · obtain ⟨y, rfl⟩ := e.surjective x
    rw [e.symm_apply_apply]
    exact hcomp y

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ : GL (Fin n) E), γ ∈ UE E n → γ.val.charpoly ∈ Ell E n → ∀ m : E[X], (∀ w : Pl E, ¬ IsSplitAt w → ∃ c : Matrix (Fin n) (Fin n) (w.adicCompletion E), c * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ).val * c ∧ cT (cj w) c * c = (aeval γ.val m).map (algebraMap E (w.adicCompletion E))) → ∀ (r : ℕ) (Q : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.SelfRecip E r), Q.1 ∣ γ.val.charpoly → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.invol Q (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) = (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) → ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (∀ w w' : Pl E, w.under (𝓞 (maximalRealSubfield E)) = v → w'.under (𝓞 (maximalRealSubfield E)) = v → w = w') → ∃ z : v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q, z * GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.involBase Q _ z = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.Fld Q) := by
  intro E _ _ _ hU n γ hγ hell m hloc r Q hQ _ v huniq
  classical
  obtain ⟨w, hw⟩ := exists_over (E := E) v
  have hns : ¬ IsSplitAt w := fun ⟨u, hne, hu⟩ => hne (huniq u w (hu.trans hw) hw)
  obtain ⟨c, hc1, hc2⟩ := hloc w hns
  obtain ⟨j, hj1, hj2⟩ := localEquiv hU v w hw (fun u hu => huniq u w hu hw)

  have hsep : γ.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ.val (γ⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]

  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := γ.val.map (algebraMap E (w.adicCompletion E)) with hA
  have hAsep : A.charpoly.Separable := by rw [hA, Matrix.charpoly_map]; exact hsep.map
  have hAP : A.charpoly = atPl w γ.val.charpoly := Matrix.charpoly_map _ _
  have hc1' : A * c = c * A := hc1.symm
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm A c hAsep hc1'
  have hAi : A * aeval A (atPl w r₀) = 1 := by
    rw [hA, aeval_map_mat, ← hr₀, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcA : cT (cj w) A * A = 1 := by
    have h0 : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.val * 1 * γ.val = 1 := hγ
    have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) h0
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hns, Matrix.mul_one] at this
    exact this
  have hcT : cT (cj w) A = aeval A (atPl w r₀) := by
    calc cT (cj w) A = cT (cj w) A * (A * aeval A (atPl w r₀)) := by rw [hAi, Matrix.mul_one]
      _ = aeval A (atPl w r₀) := by rw [← Matrix.mul_assoc, hcA, Matrix.one_mul]
  have hdiv : atPl w γ.val.charpoly ∣ (f.map (cj w)).comp (atPl w r₀) * f - atPl w m := by
    rw [← hAP]
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval A hAsep _ ?_
    have h2 : cT (cj w) (aeval A f) * aeval A f = aeval A (atPl w m) := by
      rw [hc2, hA, aeval_map_mat]
    rw [cT_aeval, hcT, ← aeval_comp] at h2
    rw [map_sub, map_mul, h2, sub_self]

  set k := v.adicCompletion (maximalRealSubfield E)
  let ι : w.adicCompletion E →+* k ⊗[maximalRealSubfield E] Fld Q :=
    ((inclBase Q k).toRingHom).comp j.toRingHom
  have hι1 : ∀ e : E, ι (algebraMap E _ e) = (1 : k) ⊗ₜ algebraMap E (Fld Q) e := by
    intro e
    change inclBase Q k (j (algebraMap E _ e)) = _
    rw [hj1]
    simp [inclBase]
  have hιc : ∀ y, involBase Q k (ι y) = ι (cj w y) := by
    intro y
    change involBase Q k (inclBase Q k (j y)) = inclBase Q k (j (cj w y))
    rw [hj2]
    generalize j y = t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [inclBase, involBase, invol_algebraMap]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let ib : k ⊗[maximalRealSubfield E] Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q := (involBase Q k).toRingHom
  let Φ : (w.adicCompletion E)[X] →+* k ⊗[maximalRealSubfield E] Fld Q := eval₂RingHom ι ((1 : k) ⊗ₜ alpha Q)
  let g : Fld Q →+* k ⊗[maximalRealSubfield E] Fld Q :=
    (Algebra.TensorProduct.includeRight : Fld Q →ₐ[maximalRealSubfield E] k ⊗[maximalRealSubfield E] Fld Q).toRingHom
  have hΦ : ∀ p : E[X], Φ (atPl w p) = (1 : k) ⊗ₜ AdjoinRoot.mk Q.1 p := by
    intro p
    have e : ι.comp (algebraMap E _) = g.comp (algebraMap E (Fld Q)) := RingHom.ext fun e => hι1 e
    change eval₂ ι ((1 : k) ⊗ₜ alpha Q) (p.map (algebraMap E (w.adicCompletion E))) = _
    rw [eval₂_map, e]
    refine (Polynomial.hom_eval₂ p (algebraMap E (Fld Q)) g (alpha Q)).symm.trans ?_
    change (1 : k) ⊗ₜ eval₂ (algebraMap E (Fld Q)) (alpha Q) p = _
    rw [← aeval_def]
    congr 1
    exact AdjoinRoot.aeval_eq p
  have hR : Φ (atPl w r₀) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
    rw [hΦ]
    congr 1
    have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 (hQ.trans hPr)
    rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hinv : ib (Φ f) = Φ ((f.map (cj w)).comp (atPl w r₀)) := by
    have e1 : ib.comp ι = ι.comp (cj w) := RingHom.ext fun y => hιc y
    have e2 : ib ((1 : k) ⊗ₜ alpha Q) = (1 : k) ⊗ₜ (alpha Q)⁻¹ := by
      change (1 : k) ⊗ₜ invol Q (alpha Q) = _
      rw [invol_alpha]
    change ib (eval₂ ι _ f) = eval₂ ι _ _
    rw [Polynomial.hom_eval₂, e1, e2, eval₂_comp, eval₂_map]
    exact congrArg (fun x => eval₂ (ι.comp (cj w)) x f) hR.symm
  obtain ⟨t, ht⟩ := hdiv
  have hft : f * (f.map (cj w)).comp (atPl w r₀) = atPl w m + atPl w γ.val.charpoly * t := by
    rw [← ht]; ring
  refine ⟨Φ f, ?_⟩
  change Φ f * ib (Φ f) = _
  have h0 : Φ (atPl w γ.val.charpoly) = 0 := by
    rw [hΦ]
    exact (congrArg _ (AdjoinRoot.mk_eq_zero.2 hQ)).trans (TensorProduct.tmul_zero _ _)
  rw [hinv, ← map_mul, hft, map_add (f := _), map_mul, h0, zero_mul, add_zero, hΦ]

end GlobalTheory.NormInert
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_iso_cross_powers_of_pullback_powers : ∀ (X Y : Scheme.{0}) (b : Y ⟶ X) (A A' : LB X) (N : LB Y) (p q : ℤ) (w : LB.Iso (GlobalTheory.AbLaw.pw N p) (A.pull b)) (w' : LB.Iso (GlobalTheory.AbLaw.pw N q) (A'.pull b)), A.IsLB → A'.IsLB → N.IsLB → w.IsGen → w'.IsGen → ∃ c : LB.Iso ((GlobalTheory.AbLaw.pw A q).pull b) ((GlobalTheory.AbLaw.pw A' p).pull b), c.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : A.ι) (k' : A'.ι) (l : N.ι), b (r z) ∈ A.U k → b (r z) ∈ A'.U k' → r z ∈ N.U l → Geo.Tor.gw c r z k' (fun _ => k) = Geo.Tor.gw w' r z k' l ^ p * (Geo.Tor.gw w r z k l ^ q)⁻¹ := by
  first | exact @GlobalTheory.FormalAlg.exists_crossIso | exact GlobalTheory.FormalAlg.exists_crossIso | (intros; apply GlobalTheory.FormalAlg.exists_crossIso <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_local_frames_of_pullback_power_on_nonzeroLocus : ∀ (X X₀ : Scheme.{0}) (γ : X₀ ⟶ X) (H₀ : LB X₀) (s : LB.Sec H₀) (k : ℕ) (L : LB X), L.IsLB → H₀.IsLB → ∀ (w : LB.Iso (L.pull γ) (pw H₀ k)), w.IsGen → ∀ (D : X.Opens), γ ⁻¹ᵁ D = nonzeroLocus s → ∃ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) ∧ ∀ z m a, γ z ∈ D ⊓ L.U m → z ∈ H₀.U a → gs (𝟙 X₀) z _ (s.f a) ^ k = (gm (𝟙 X₀) z _ (u m)).val * (gm (𝟙 X₀) z _ (w.s (a, fun _ => m))).val := by
  first | exact @GlobalTheory.Div.FramePull.frame_pull | exact GlobalTheory.Div.FramePull.frame_pull | (intros; apply GlobalTheory.Div.FramePull.frame_pull <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  first
  | exact @GlobalTheory.EtC.eqv_sch_of_stalks
  | exact GlobalTheory.EtC.eqv_sch_of_stalks
  | (intros; apply GlobalTheory.EtC.eqv_sch_of_stalks <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpLin

theorem exists_ringHom_matrix_lift : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  intro X G _ _ g O _ act hab hsm hhom h1 hmul hadd y e he
  have H := fun a => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism X G g hab hsm y e e (act a) he he (hhom a)
  let M : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => (H a).exists.choose
  have hM : ∀ a z, e (M a z) = e z ≫ act a := fun a => (H a).exists.choose_spec
  have key : ∀ a (N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, e (N z) = e z ≫ act a) → N = M a :=
    fun a N hN => (H a).unique hN (hM a)
  have M1 : M 1 = LinearMap.id := (key 1 LinearMap.id (fun z => by simp [h1])).symm
  have Mmul : ∀ a b, M (a * b) = M a ∘ₗ M b := fun a b =>
    (key (a * b) (M a ∘ₗ M b) (fun z => by
      simp only [LinearMap.comp_apply, hM, hmul, Category.assoc])).symm
  have Madd : ∀ a b, M (a + b) = M a + M b := fun a b =>
    (key (a + b) (M a + M b) (fun z => by
      rw [LinearMap.add_apply, he.1, hM, hM, hadd, MonObj.comp_mul])).symm
  let f : O →* Matrix (Fin g) (Fin g) ℂ :=
    { toFun := fun a => LinearMap.toMatrix' (M a)
      map_one' := by simp only [M1, LinearMap.toMatrix'_id]
      map_mul' := fun a b => by simp only [Mmul, LinearMap.toMatrix'_comp] }
  refine ⟨RingHom.mk' f (fun a b => by simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Madd, map_add (f := _)]), ?_⟩
  intro a z
  show e (LinearMap.toMatrix' (M a) *ᵥ z) = _
  rw [LinearMap.toMatrix'_mulVec, hM]

end GlobalTheory.ExpLin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.PELU

theorem exists_linMap_of_periods {O : Type} [Ring O] {bar : O → O} {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D₁ D₂ : PLat O bar) (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ))
    (hP : ∀ (a : O) x, P (a • x) = ρ a *ᵥ P x) (hP' : ∀ (a : O) x, P' (a • x) = ρ a *ᵥ P' x)
    (hinj : Function.Injective P') (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hr : ∀ x, ∃ y, P' y = h (P x))
    (hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z) :
    ∃ w : D₁.La →ₗ[O] D₂.La, ∀ x, P' (w x) = h (P x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply hinj
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, hP', hf, hf, hP, hc]

theorem int_eq_of_exp_eq (m n : ℤ)
    (H : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  set k : ℕ := (n - m).natAbs + 1 with hkdef
  have hk : 0 < k := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (H k hk)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have E : ((n - m : ℤ) : ℂ) = ((j * k : ℤ) : ℂ) := by
    push_cast
    field_simp at hj
    linear_combination hj
  have E' : n - m = j * k := by exact_mod_cast E
  have hd : (k : ℤ) ∣ n - m := ⟨j, by rw [E', mul_comm]⟩
  have h0 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by rw [Int.natAbs_natCast]; omega)
  omega

theorem unifAt_cmp : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e e' hN U1 U2
  obtain ⟨-, hper1, hexp1, hker1, hact1, hweil1, heta1⟩ := U1
  obtain ⟨-, hper2, hexp2, hker2, hact2, hweil2, heta2⟩ := U2
  have lift := fun (e₁ e₂ : (Fin g → ℂ) → (Over.mk y ⟶ F.A)) (α : F.A ⟶ F.A) (h1 : IsExp y e₁) (h2 : IsExp y e₂)
    (hα : IsMonHom α) => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism F.X F.A g F.ab F.dim y e₁ e₂ α h1 h2 hα
  obtain ⟨M, hM, -⟩ := lift e e' (𝟙 _) hexp1 hexp2 inferInstance
  obtain ⟨M', hM', -⟩ := lift e' e (𝟙 _) hexp2 hexp1 inferInstance
  simp only [Category.comp_id] at hM hM'
  have h1 : M'.comp M = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e e (𝟙 _) hexp1 hexp1 inferInstance
    rw [hK (M'.comp M) (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  have h2 : M.comp M' = LinearMap.id := by
    obtain ⟨K, -, hK⟩ := lift e' e' (𝟙 _) hexp2 hexp2 inferInstance
    rw [hK (M.comp M') (fun z => by simp [hM', hM]), hK LinearMap.id (fun z => by simp)]
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofLinear M M' h2 h1
  have hh : ∀ z, e' (h z) = e z := hM
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ P'.range := fun z => by rw [← hker1, ← hker2, hh]
  have hc : ∀ (a : O) z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    obtain ⟨K, -, hK⟩ := lift e e' (F.act a) hexp1 hexp2 (F.hom a)
    have k1 := hK ((h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp (Matrix.mulVecLin (ρ a)))
      (fun z => by simp [hh, hact1])
    have k2 := hK ((Matrix.mulVecLin (ρ a)).comp (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)))
      (fun z => by simp [hact2, hh])
    have := congrArg (fun f : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) => f z) (k1.trans k2.symm)
    simpa using this
  have hc' : ∀ (a : O) z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    apply h.injective
    rw [hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  obtain ⟨w₁, hw₁⟩ := exists_linMap_of_periods ρ D' D'' P P' hper1.1 hper2.1 hper2.2.1 h
    (fun x => (AddMonoidHom.mem_range).mp ((hrange (P x)).mp ⟨x, rfl⟩)) hc
  obtain ⟨w₂, hw₂⟩ := exists_linMap_of_periods ρ D'' D' P' P hper2.1 hper1.1 hper1.2.1 h.symm
    (fun x => (AddMonoidHom.mem_range).mp ((hrange _).mpr (by rw [LinearEquiv.apply_symm_apply]; exact ⟨x, rfl⟩))) hc'
  let w : D'.La ≃ₗ[O] D''.La := LinearEquiv.ofLinear w₁ w₂
    (LinearMap.ext fun x => hper2.2.1 (by simp [hw₁, hw₂]))
    (LinearMap.ext fun x => hper1.2.1 (by simp [hw₁, hw₂]))
  have hw : ∀ x, P' (w x) = h (P x) := hw₁
  refine ⟨w, h, ⟨?_, ?_⟩, hw, hh⟩
  · intro x x'
    refine (int_eq_of_exp_eq _ _ fun k hk => ?_)
    have H1 := hweil1 k x x' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have H2 := hweil2 k (w x) (w x') (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    rw [hw, hw, ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hh, hh] at H2
    have := GlobalTheory.T.weilPairing_complex_value_unique F.X F.A g F.ab F.dim F.L F.isLB y k _ _ _ _ H2 H1
    simpa using congrArg Units.val this
  · intro a
    have e0 : e' 0 = 1 := (hker2 0).mpr (zero_mem _)
    set v := (N : ℂ)⁻¹ • P' (t' a)
    set u := (N : ℂ)⁻¹ • P' (w (t a)) - v
    have huv : e' (u + v) = e' v := by
      rw [sub_add_cancel, hw, ← LinearEquiv.map_smul, hh, ← heta1, heta2]
    have hu : e' u = 1 := by
      have := (hexp2.1 (u + v) (-v)).symm
      rw [add_neg_cancel_right, huv, ← hexp2.1, add_neg_cancel, e0] at this
      exact this.symm
    obtain ⟨x₀, hx₀⟩ := (hker2 u).mp hu
    refine ⟨x₀, ?_⟩
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    apply hper2.2.1
    have : P' (w (t a)) - P' (t' a) = (N : ℂ) • u := by
      simp only [u, v, ← smul_sub, smul_smul, mul_inv_cancel₀ hN', one_smul]
    rw [map_add (f := _), map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, hx₀, ← this]
    abel

end GlobalTheory.PELU
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.exists_standard_charts_formalTower_of_veryAmple : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  first | exact @GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy | exact GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy | (intros; apply GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

theorem _root_.GlobalTheory.T.thickeningTowerCharts_preimage_and_germ_pullback : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (n : ℕ) (C : Charts I Y β n) (γ : ∀ e, (Y 0).left ⟶ (Y e).left), γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ (e : ℕ) (i : Fin (n + 1)), γ e ⁻¹ᵁ C.D e i = C.D 0 i ∧ ∀ (j : Fin (n + 1)) (z : (Y 0).left), z ∈ C.D 0 i → gs (γ e) z (C.D e i) (C.ρ e i j) = gs (𝟙 _) z (C.D 0 i) (C.ρ 0 i j) := by
  first | exact @GlobalTheory.FormalAlg.Charts.tower_preimage_germ | exact GlobalTheory.FormalAlg.Charts.tower_preimage_germ | (intros; apply GlobalTheory.FormalAlg.Charts.tower_preimage_germ <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cech_cohomology_structure_sheaf_iso : ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ Sp K) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Nonempty (HO1 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 1) ∧ Nonempty (HO2 s ≃ₗ[K] (cechLB s (LB.triv X) D).homology 2) := by
  first | exact @GlobalTheory.AbCoh.hO_equiv_cech | exact GlobalTheory.AbCoh.hO_equiv_cech | (intros; apply GlobalTheory.AbCoh.hO_equiv_cech <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_abelian | exact GlobalTheory.AbCoh.primF_of_abelian | (intros; apply GlobalTheory.AbCoh.primF_of_abelian <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  first | exact @GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes | exact GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes | (intros; apply GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.structure_cohomology_flat_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  first | exact @GlobalTheory.AbCoh.flat_baseChange_HO | exact GlobalTheory.AbCoh.flat_baseChange_HO | (intros; apply GlobalTheory.AbCoh.flat_baseChange_HO <;> assumption)
end
