module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle104
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb

open GlobalTheory.UnitLemma

def intVec (K : UQ) (n : ℕ) : Submodule K.O (Fin n → K.E) where
  carrier := {v | ∀ i, v i ∈ (algebraMap K.O K.E).range}
  add_mem' := fun ha hb i => Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun _ => Subring.zero_mem _
  smul_mem' := fun c v hv i => by
    simp only [Pi.smul_apply, Algebra.smul_def]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hv i)

def modelLat {K : UQ} (B : InvAlg K) {n : ℕ} (ψ : B.A ≃ₗ[K.E] (Fin n → K.E))
    (P : Matrix (Fin n) (Fin n) K.E) : Submodule K.O B.A :=
  (intVec K n).comap ((Matrix.toLin' P).restrictScalars K.O ∘ₗ ψ.toLinearMap.restrictScalars K.O)

def unitLat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} {K : UQ}
    (e : K.E ≃+* w.adicCompletion E) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (q : UL n w) :
    Submodule K.O B.A :=
  modelLat B ψ ((((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm)

end GlobalTheory.InertUnitOrb
end
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

def unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ) (hσ : ∀ a, σ' (incF c c' hle a) = σ a)
    (U : Unf Xo c σ r) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := σ.toAlgebra
  { Comp := U.Comp
    fin := U.fin
    X := U.X
    un := fun k x => FrPt.ext hle (S := CAt σ') hσ (U.un k x) }

def covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) : DeltaDat Xo c' n :=
  { ddBC hle d with cδ := ((show (covCoeff hle d).F from u) • rulBC (le_covCoeff hle d) d.cδ : Rul d.Xo₂ (covCoeff hle d)) }

def covUnf (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) :
    Unf (covBC hle d u).Xo₂ (covBC hle d u).c₂
      (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) r :=
  unfExt (le_covCoeff hle d) _ (fun _ => rfl) U₂

end Gen

section Val

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}

def CXiAt {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) : Prop :=
  IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif d.Xo₂ ((σ0.comp (d.eF.symm : d.c₂.F →+* c.F)).comp
          (IntermediateField.inclusion d.c₂.le).toRingHom)
        (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
      (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
      (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
        rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2 =
          c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

theorem cXiVal_iff {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 dδ U₂ dict₂ ι x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, CXiAt V hr σ0 (dδ t) (U₂ t) (dict₂ t) ι x₀ (xi t) c0 := Iff.rfl

end Val

end GlobalTheory.OneMapAll
end
end

section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.WeylUnipotentShell

section BlockKeep

variable {R : Type} [CommRing R] {n : ℕ}

def blockKeep (a b : Fin n) (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  fun i j => if (a ≤ i ∧ i ≤ b) ∧ (a ≤ j ∧ j ≤ b) then A i j else (1 : Matrix (Fin n) (Fin n) R) i j

theorem blockKeep_one (a b : Fin n) : blockKeep a b (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j; unfold blockKeep; split_ifs <;> rfl

theorem blockKeep_mul (a b : Fin n) (A B : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : blockKeep a b (A * B) = blockKeep a b A * blockKeep a b B := by
  ext i j
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · simp only [blockKeep, Matrix.mul_apply, if_pos (And.intro hi hj)]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : a ≤ k ∧ k ≤ b
      · rw [if_pos ⟨hi, hk⟩, if_pos ⟨hk, hj⟩]
      · rw [if_neg (fun h => hk h.2), Matrix.one_apply_ne (by rintro rfl; exact hk hi), zero_mul]
        rcases not_and_or.1 hk with h | h
        · rw [hA i k (lt_of_lt_of_le (not_le.1 h) hi.1), zero_mul]
        · rw [hB k j (lt_of_le_of_lt hj.2 (not_le.1 h)), mul_zero]
    · have hcol : ∀ k, blockKeep a b B k j = (1 : Matrix (Fin n) (Fin n) R) k j := fun k => if_neg (fun h => hj h.2)
      rw [Matrix.mul_apply]
      simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      simp only [blockKeep, hi, hj, and_false, if_false, true_and, Matrix.one_apply]
  · have hrow : ∀ k, blockKeep a b A i k = (1 : Matrix (Fin n) (Fin n) R) i k := fun k => if_neg (fun h => hi h.1)
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [blockKeep, hi, false_and, if_false, Matrix.one_apply]

end BlockKeep

section Keep

variable {L : Type} [Field L] {n : ℕ}

def blockKeepGL (a b : Fin n) (g : GL (Fin n) L) (hg : g ∈ unipB L (Fin n)) : GL (Fin n) L where
  val := blockKeep a b (g : Matrix (Fin n) (Fin n) L)
  inv := blockKeep a b ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  val_inv := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 hg).1 ((mem_unipB L).1 (inv_mem hg)).1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, blockKeep_one]
  inv_val := by
    rw [← blockKeep_mul a b _ _ ((mem_unipB L).1 (inv_mem hg)).1 ((mem_unipB L).1 hg).1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, blockKeep_one]

theorem blockKeepGL_mem_GU [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} (a : Fin n) (g : GL (Fin n) L)
    (hg : g ∈ unipB L (Fin n)) (hG : g ∈ GU σ n) : blockKeepGL a a.rev g hg ∈ GU σ n := by
  rw [LGrp.mem_GU_iff] at hG ⊢
  intro i j
  show blockKeep a a.rev ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
    σ (blockKeep a a.rev (g : Matrix (Fin n) (Fin n) L) j.rev i.rev)
  have key : ∀ i : Fin n, (a ≤ i.rev ∧ i.rev ≤ a.rev) ↔ (a ≤ i ∧ i ≤ a.rev) := by
    intro i
    have := i.isLt
    have := a.isLt
    simp only [Fin.le_iff_val_le_val, Fin.val_rev]
    omega
  unfold blockKeep
  simp only [key]
  by_cases h : (a ≤ i ∧ i ≤ a.rev) ∧ (a ≤ j ∧ j ≤ a.rev)
  · rw [if_pos h, if_pos h.symm, hG]
  · rw [if_neg h, if_neg (fun h' => h h'.symm), Matrix.one_apply, Matrix.one_apply, apply_ite σ, map_one, map_zero]
    simp only [Fin.rev_inj, eq_comm (a := j)]

theorem blockKeep_eq_self (a b : Fin n) (A : Matrix (Fin n) (Fin n) L) (h1 : ∀ i j, j < i → A i j = 0)
    (h2 : ∀ i, A i i = 1) (h3 : ∀ i j, i < j → (i < a ∨ b < j) → A i j = 0) : blockKeep a b A = A := by
  ext i j
  unfold blockKeep
  split_ifs with h
  · rfl
  · rcases lt_trichotomy i j with hij | rfl | hij
    · rw [Matrix.one_apply_ne hij.ne, h3 i j hij]
      by_contra hc
      rw [not_or, not_lt, not_lt] at hc
      exact h ⟨⟨hc.1, hij.le.trans hc.2⟩, hc.1.trans hij.le, hc.2⟩
    · rw [Matrix.one_apply_eq, h2]
    · rw [Matrix.one_apply_ne hij.ne', h1 i j hij]

end Keep

end GlobalTheory.WeylCell.WeylUnipotentShell
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory

theorem Twist.exists_secs_generating_ideal : ∀ (X : Scheme.{0}) (M : LB X), M.IsLB → ∀ (I : X.IdealSheafData), IsGloballyGenerated (twist (idealModule I) M) → ∃ (n : ℕ) (σ : Fin n → M.Sec), (∀ (k : Fin n) (i : M.ι) (W : X.affineOpens) (h : W.1 ≤ M.U i), resG X h ((σ k).f i) ∈ I.ideal W) ∧ ∀ (x : X) (i : M.ι) (hx : x ∈ M.U i) (W : X.affineOpens) (hxW : x ∈ W.1) (a : Γ(X, W.1)), a ∈ I.ideal W → X.presheaf.germ W.1 x hxW a ∈ Ideal.span (Set.range fun k => X.presheaf.germ (M.U i) x hx ((σ k).f i)) := by
  intro X M hM I hg
  obtain ⟨n, a, ha⟩ := isGloballyGenerated_iff_spanStalks.1 hg
  refine ⟨n, fun k => Twist.secOfTwist (idealModuleι I) (a k), ?_, ?_⟩
  · intro k i W h
    have hW : W.1 ≤ ⊤ ⊓ M.U i := le_inf le_top h
    rw [Twist.secOfTwist_f, LB.resG_resG]
    refine (exists_idealModuleι_app_eq_iff_mem I W _).1
      ⟨Twist.resM _ hW (Twist.coord (a k) i), ?_⟩
    rw [Twist.app_resM]
    exact structureModuleSectionsEquiv_res hW _
  · intro x i hx W hxW f hf
    obtain ⟨t, rfl⟩ := (exists_idealModuleι_app_eq_iff_mem I W f).2 hf
    let l := (structureModuleStalkEquiv x).toLinearMap ∘ₗ stalkLinear (idealModuleι I) x ∘ₗ
      (Twist.stalkEquiv (idealModule I) hM i hx).toLinearMap
    have hm : x ∈ ⊤ ⊓ M.U i := ⟨trivial, hx⟩
    have e : (l ∘ fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
        ((twist (idealModule I) M).presheaf.stalk x :))) =
        fun k => X.presheaf.germ (M.U i) x hx ((Twist.secOfTwist (idealModuleι I) (a k)).f i) := by
      funext k
      rw [Twist.secOfTwist_f, X.presheaf.germ_res_apply (homOfLE _) x hx]
      rw [Function.comp_apply, ← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
      exact congrArg (fun u => structureModuleStalkEquiv x (stalkLinear (idealModuleι I) x u))
        (Twist.stalkEquiv_germ hM i hx (V := ⊤) trivial (a k))
    have hu : X.presheaf.germ W.1 x hxW
        (structureModuleSectionsEquiv W.1 ((idealModuleι I).app W t)) =
        l ((Twist.stalkEquiv (idealModule I) hM i hx).symm
          ((idealModule I).presheaf.germ W.1 x hxW t)) := by
      simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        stalkLinear_germ, structureModuleStalkEquiv_germ]
    have hmem : (Twist.stalkEquiv (idealModule I) hM i hx).symm
        ((idealModule I).presheaf.germ W.1 x hxW t) ∈ Submodule.span (X.presheaf.stalk x)
          (Set.range fun k => ((twist (idealModule I) M).presheaf.germ ⊤ x trivial (a k) :
            ((twist (idealModule I) M).presheaf.stalk x :))) := by
      rw [ha x]; exact Submodule.mem_top
    have h2 := Submodule.apply_mem_span_image_of_mem_span l hmem
    rw [← Set.range_comp, e] at h2
    rw [hu]
    exact h2

end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isCompact_krylov_units : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  intro E _ _ w r Ω hΩ hcov
  classical
  let kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E) :=
    fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e
  have hkc : ∀ e, Continuous (kr e) := by
    intro e
    have hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E)) :=
      Units.continuous_val
    refine continuous_matrix fun i j => ?_
    simp only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]
    exact (continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)
  let U : (Fin r → w.adicCompletion E) → Set (GLw r w) := fun e => {y | (kr e y).det ≠ 0}
  have hU : ∀ e, IsOpen (U e) := fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const
  have hsub : Ω ⊆ ⋃ e, U e := by
    intro y hy
    obtain ⟨e, he⟩ := hcov y hy
    exact Set.mem_iUnion.2 ⟨e, he.ne_zero⟩
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover U hU hsub
  obtain ⟨K, hKc, hKU, hΩK⟩ := hΩ.finite_compact_cover t U (fun e _ => hU e) ht
  have hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1) := fun e y =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))
  let f : ∀ e, K e → GLw r w := fun e y => (hunit e y).unit
  have hf : ∀ e, Continuous (f e) := by
    intro e
    rw [Units.continuous_iff]
    constructor
    · exact (hkc e).comp continuous_subtype_val
    · have : (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹ := by
        funext y
        rw [Matrix.coe_units_inv]
        rfl
      rw [this]
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul
        ((hkc e).comp continuous_subtype_val).matrix_adjugate
  refine ⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 (hKc e)
    exact isCompact_range (hf e)
  · intro y hy
    rw [hΩK] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨e, he, hyK⟩ := hy
    exact ⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩

end GlobalTheory.LeviDesc.Krylov
end
end

section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

theorem colGL_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    ((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem colGL_inv_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    (((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem norm_one_apply_le' {a : ℕ} (i j : Fin a) : ‖(1 : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem norm_ite_apply_le {a : ℕ} (p : Prop) [Decidable p] (x : Fin a → ℂ) (i : Fin a) :
    ‖(if p then x i else 0)‖ ≤ ‖x‖ := by
  split_ifs
  · exact norm_le_pi_norm x i
  · simp

theorem htGL_colGL_le {a : ℕ} (r : ℕ) (x : Fin a → ℂ) :
    htGL (colGL r x) ≤ 1 + 2 * (a : ℝ) ^ 2 * (1 + ‖x‖) := by
  unfold htGL
  have h1 : ∀ i j : Fin a, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_val_apply]
    exact (norm_add_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have h2 : ∀ i j : Fin a, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_inv_val_apply]
    exact (norm_sub_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have s1 : ∑ i, ∑ j, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have s2 : ∑ i, ∑ j, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith

theorem norm_inr_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inr ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

theorem norm_inl_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inl ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

end GlobalTheory.JSW
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.DiagThetaRatInv

theorem dot_elim {R : Type} [CommRing R] {κ : Type} [Fintype κ] (x : κ ⊕ κ → R) (v : κ → R) :
    x ⬝ᵥ Sum.elim v (-v) = ∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, sub_mul,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem schr_diag {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (u v : κ → R) (Φ : (κ ⊕ κ → R) → ℂ) (x : κ ⊕ κ → R) :
    GlobalTheory.WeilM.schr ψ (Sum.elim u u, Sum.elim v (-v)) Φ x =
      ψ (∑ i, (x (Sum.inl i) - x (Sum.inr i)) * v i) * Φ (x + Sum.elim u u) := by
  simp only [GlobalTheory.WeilM.schr]
  rw [dot_elim, dot_elim]
  simp

theorem diag_theta_rat_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ]
    (Φ : (κ ⊕ κ → AF F) → ℂ), ∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w : (κ → AF F) × (κ → AF F),
      GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim (γ + w).1 (γ + w).1, Sum.elim (γ + w).2 (-(γ + w).2)) Φ) =
        GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (Sum.elim w.1 w.1, Sum.elim w.2 (-w.2)) Φ) := by
  intro F _ _ ψ hψ κ _ Φ γ hγ w
  obtain ⟨a, b, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff γ).1 hγ
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [← (Equiv.subRight (Sum.elim a a)).tsum_eq]
  congr 1
  funext η
  rw [schr_diag, schr_diag]
  simp only [Equiv.subRight_apply, Prod.fst_add, Prod.snd_add]
  have h1 : (∑ i, (algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inl i)) -
        algebraMap F (AF F) ((η - Sum.elim a a) (Sum.inr i))) * ((fun i => algebraMap F (AF F) (b i)) + w.2) i) =
      algebraMap F (AF F) (∑ i, (η (Sum.inl i) - η (Sum.inr i)) * b i) +
        ∑ i, (algebraMap F (AF F) (η (Sum.inl i)) - algebraMap F (AF F) (η (Sum.inr i))) * w.2 i := by

    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, map_sub, map_mul]
    ring
  have h2 : (fun i => algebraMap F (AF F) ((η - Sum.elim a a) i)) +
        Sum.elim ((fun i => algebraMap F (AF F) (a i)) + w.1) ((fun i => algebraMap F (AF F) (a i)) + w.1) =
      (fun i => algebraMap F (AF F) (η i)) + Sum.elim w.1 w.1 := by
    funext j
    cases j <;> simp <;> abel
  rw [h1, h2, AddChar.map_add_eq_mul, hψ.2.2.1, one_mul]

end GlobalTheory.DiagThetaRatInv
end
