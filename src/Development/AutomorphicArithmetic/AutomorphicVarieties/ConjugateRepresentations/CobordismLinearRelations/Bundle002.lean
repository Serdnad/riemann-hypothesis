module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rT_adj (r : ℝ) (x : GL (Fin a) (Af E)) (X : Lie E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smAdj Ξ r X m) = smAdj Ξ r X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
  have h : lie E a X * act (.fin x) = act (.fin x) * lie E a X := lie_rt_fin X x
  have h1 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smA Ξ X m) = smA Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smA_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.rTensor_mul, ← LinearMap.rTensor_mul, h]
  have h2 : (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (smB Ξ X m) = smB Ξ X ((act (.fin x)).rTensor (Fin Ξ.d → ℂ) m) := by
    rw [smB_apply]
    clear h1
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
    | tmul φ v => simp
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, LinearMap.map_smul_of_tower]

variable {π : CuspSub E a} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem cocl_comb {q : ℕ} (s : ℂ) {ω η : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω)
    (hη : Coclosed (smAdj Ξ r) e η) : Coclosed (smAdj Ξ r) e (s • ω + η) := by
  have ap : ∀ X, (s • ω + η) X = s • ω X + η X := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

private theorem cocl_zero {q : ℕ} : Coclosed (smAdj Ξ r) e (0 : Geo.Co Ξ q) := by
  cases q with
  | zero => trivial
  | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem cocl_trans {q : ℕ} (x : GL (Fin a) (Af E)) {ω : Geo.Co Ξ q} (hω : Coclosed (smAdj Ξ r) e ω) :
    Coclosed (smAdj Ξ r) e (Geo.trans x ω) := by
  have ap : ∀ X, Geo.trans x ω X = (act (.fin x)).rTensor (Fin Ξ.d → ℂ) (ω X) := fun X => rfl
  cases q with
  | zero => trivial
  | succ q =>
    refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω) X
    rw [del_apply, AlternatingMap.zero_apply] at h1 ⊢

    simp only [ap, ← rT_adj, ← map_sum, h1, map_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.harmSub :
    UpperTheory.V.Cj.HarmSub := by
  intro E _ _ _ a π Ξ r n e q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsPiHarm π Ξ r e α → IsPiHarm π Ξ r e β → IsPiHarm π Ξ r e (s • α + β) :=
    fun s α β hα hβ => ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.1)) ((L1 _).2 hβ.1)),
      by rw [dCo_comb, hα.2.1, hβ.2.1, smul_zero, add_zero], cocl_comb s hα.2.2.1 hβ.2.2.1,
      fun X => Submodule.add_mem _ (Submodule.smul_mem _ s (hα.2.2.2 X)) (hβ.2.2.2 X)⟩
  have zero : IsPiHarm π Ξ r e (0 : Geo.Co Ξ q) :=
    ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], cocl_zero, fun X => Submodule.zero_mem _⟩
  refine ⟨{ carrier := {ω | IsPiHarm π Ξ r e ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ },
    fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, cocl_trans x h3, fun X => mem_tens.2 fun i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact π.stable (.fin x) _ (mem_tens.1 (h4 X) i)
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (a n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    {χ : HChar E} (hχ : χ.IsAbsPow (((n : ℝ) - a) / 2)) (B : Multiset ℂˣ) :
    algSat n (Formalism.ConjugateSelfDual.normV w) (B.map (· * χ.val w)) = algSat a (Formalism.ConjugateSelfDual.normV w) B := by
  have h := hχ.2.1 w
  have hq : (0 : ℝ) < (Formalism.ConjugateSelfDual.normV w : ℕ) := by
    have he : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    rw [he]
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [algSat_eq, algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  rw [h]
  have e : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := by
    first | rfl | exact Ideal.absNorm_apply _ | simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have e2 : ((a : ℝ) - 1) / 2 = ((n : ℝ) - 1) / 2 + -(((n : ℝ) - a) / 2) := by ring
  rw [e, e2, Real.rpow_add hq, Complex.ofReal_mul, Complex.ofReal_cpow hq.le (-_), Complex.ofReal_neg,
    Complex.ofReal_natCast]
  ring

theorem UpperTheory.V.Cj.blockConj :
    UpperTheory.V.Cj.BlockConj := by
  intro E _ _ _ a n hC π μ m h1 h2 h3 σ
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((n : ℝ) - a) / 2)
  have hν' := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((a : ℝ) - n) / 2)
  obtain ⟨π', hπ'⟩ := satConj E n hC _ (twReg E a n π μ m h1 h2 h3 _ hν) σ
  refine ⟨π'.twist (GlobalTheory.HeckeGal.Model.absPow E (((a : ℝ) - n) / 2)), fun w B hB => ?_⟩
  obtain ⟨B', b1, b2⟩ := hπ' w _ (sat_twist π hB (hν.1 w))
  refine ⟨_, sat_twist π' b1 (hν'.1 w), ?_⟩
  rw [algSat_shift n a w hν', b2, algSat_shift a n w hν]
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.irrCo :
    UpperTheory.V.Cj.IrrCo := by
  intro E _ _ _ a π τ hτ Ξ q P hP hst hV
  haveI : Nontrivial P := Submodule.nontrivial_iff_ne_bot.2 hP
  haveI : Module.Finite ℝ (Herm E a) := inferInstance
  let b := Module.finBasis ℝ (Herm E a)
  let ρW : Representation ℂ (GL (Fin a) (Af E)) P :=
    { toFun := fun x => (transRep Ξ q x).restrict (fun ω hω => hst x ω hω)
      map_one' := LinearMap.ext fun w => Subtype.ext (by simp)
      map_mul' := fun x y => LinearMap.ext fun w =>
        Subtype.ext (LinearMap.congr_fun (map_mul (transRep Ξ q) x y) w.1) }
  let p : (Fin q → Fin (Module.finrank ℝ (Herm E a))) × Fin Ξ.d → P →ₗ[ℂ] π.V := fun j =>
    { toFun := fun w => ⟨Bor.cmp j.2 (w.1 fun k => b (j.1 k)), mem_tens.1 (hV w.1 w.2 _) j.2⟩
      map_add' := fun x y => Subtype.ext (by
        change Bor.cmp j.2 ((x.1 + y.1) _) = Bor.cmp j.2 _ + Bor.cmp j.2 _
        rw [AlternatingMap.add_apply, map_add (f := _)])
      map_smul' := fun c x => Subtype.ext (by
        change Bor.cmp j.2 ((c • x.1) _) = c • Bor.cmp j.2 _
        rw [AlternatingMap.smul_apply, map_smul]) }
  obtain ⟨Φ, h1, h2⟩ := irrAbs _ τ.V π.V P _ τ.ρ π.finPart ρW τ.irred hτ.iSup_range p
    (fun j g w => Subtype.ext (cmp_trans g w.1 _ j.2))
    (fun w hw => Subtype.ext (by
      refine Module.Basis.ext_alternating b fun v _ => ?_
      rw [← sum_cmp (w.1 _)]
      have : ∀ i, Bor.cmp i (w.1 fun k => b (v k)) = 0 := fun i => congrArg Subtype.val (hw (v, i))
      simp [this]))
  exact ⟨P.subtype ∘ₗ Φ, P.subtype_injective.comp h1, fun v => (Φ v).2, fun g v => congrArg Subtype.val (h2 g v)⟩
end
