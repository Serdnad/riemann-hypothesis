module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle082
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.SliceBdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.TensEig
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S Formalism.UG.P
open GroundTheory.Automorphic.AutomorphicForm (archCompact infEmb)

private theorem ty_comm {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Submodule ℂ (Kinf E a → ℂ))
    [FiniteDimensional ℂ W] (T : Module.End ℂ (Sm E a)) (hT : ∀ k, Commute T (cptRep E a k)) (φ : Sm E a)
    (h : ∀ g, (fun k : Kinf E a => φ.1 (g * infGL E a (Unitary.toUnits k))) ∈ W) (g) :
    (fun k : Kinf E a => (T φ).1 (g * infGL E a (Unitary.toUnits k))) ∈ W := by
  let e := LinearEquiv.funCongrLeft ℂ ℂ (UpperTheory.V.Cm.cptEq E a).symm.toEquiv
  have key : ∀ (ψ : Sm E a) g, e (fun k : Kinf E a => ψ.1 (g * infGL E a (Unitary.toUnits k))) =
      fun k : archCompact E a => ψ.1 (g * infEmb E a k.1) := fun ψ g => funext fun k => by
    obtain ⟨k, rfl⟩ := (UpperTheory.V.Cm.cptEq E a).surjective k
    rw [UpperTheory.V.Cm.infEmb_cptEq]
    simp [e, LinearMap.funLeft]
  have h1 := typesComm E a (W.map e.toLinearMap) inferInstance T hT φ (fun g => ⟨_, h g, key φ g⟩) g
  obtain ⟨f, hf, e1⟩ := h1
  rwa [← e.injective (e1.trans (key (T φ) g).symm)]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.stabT :
    StabT := by
  intro E _ _ _ a bad L W hL hW S hS hty
  obtain ⟨h1, h2, h3⟩ := hullOps capAct E a S
  have hb := hullBdd typesComm E a S hS L hL.isOpen
  have hK : ∀ w ∉ bad, fixed (finRep E a) L ≤ fixed (fL a w) (KGL w (n := a)) := fun w hw φ hφ =>
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => GlobalTheory.LGrp.mem_fixed.1 hφ _ (hL.loc w hw k hk)
  refine ⟨hull S ⊓ fixed (finRep E a) L, le_inf h1 fun φ hφ => ?_, ?_, fun φ hφ => ⟨?_, fun u hu g => ?_, ?_⟩,
    fun w hw => inf_le_right.trans (hK w hw), ?_⟩
  · exact GlobalTheory.LGrp.mem_fixed.2 fun u hu => Subtype.ext (funext fun g => (hty φ hφ).1 u hu g)
  · haveI := UpperTheory.V.Af.Fin.formsFinite E a _ hb
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (UpperTheory.V.Cm.smEq E a).injective _).symm
  · exact (UpperTheory.V.Cm.isAutForm_iff φ).2 (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hb _ ⟨φ, hφ, rfl⟩)
  · exact congrFun (congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hφ.2 u hu)) g
  · have h4 := hφ.1
    clear hφ
    induction h4 using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨T, hT, φ, hφ, rfl⟩ := hψ
      exact ty_comm W T hT.1 φ (hty φ hφ).2
    | zero => exact fun _ => W.zero_mem
    | add x y _ _ hx hy => exact fun g => W.add_mem (hx g) (hy g)
    | smul c x _ hx => exact fun g => W.smul_mem c (hx g)
  · rintro (⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩) φ ⟨hφ, hφ'⟩
    · refine ⟨h2 t u φ hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_⟩
      have e := LinearMap.congr_fun ((capAct E a t u).1 (finGL E a k)).eq φ
      have e' : rt E a (finGL E a k) φ = φ := GlobalTheory.LGrp.mem_fixed.1 hφ' k hk
      rw [Module.End.mul_apply, Module.End.mul_apply, e'] at e
      exact e.symm
    · have hc := Final.GLintComm E w a
      refine ⟨?_, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
      · change heckeVec (fL a w) (KGL w (n := a)) h φ ∈ hull S
        rw [heckeVec, finsum_eq_sum (fun c : _ ⧸ KGL w (n := a) => h c.out • fL a w c.out φ) (finite_heckeVec hc hh (fL a w) φ)]
        exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (h3 _ φ hφ)
      · change finRep E a u (heckeVec (fL a w) (KGL w (n := a)) h φ) = heckeVec (fL a w) (KGL w (n := a)) h φ
        have hk := hL.int u hu w
        obtain ⟨u', hu', e1, e3⟩ : ∃ u' ∈ L, GeneralLinearGroup.map (pLoc E w) u' = 1 ∧
            u = locGL E a w (GeneralLinearGroup.map (pLoc E w) u) * u' :=
          ⟨_, L.mul_mem (L.inv_mem (hL.loc w hw _ hk)) hu, by rw [map_mul, map_inv, pLoc_locGL, inv_mul_cancel],
            (mul_inv_cancel_left _ _).symm⟩
        have e2 := map_heckeVec hc hh (ρ := fL a w) (ρ' := fL a w) (finRep E a u') (fun g y => by
          change finRep E a u' (finRep E a (locGL E a w g) y) = finRep E a (locGL E a w g) (finRep E a u' y)
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
            LocUniq.comm_locGL w e1]) φ
        rw [e3, map_mul, Module.End.mul_apply, e2, GlobalTheory.LGrp.mem_fixed.1 hφ' u' hu']
        exact GlobalTheory.LGrp.mem_fixed.1 (SatCompare.heckeVec_mem_fixed hc hh (hK w hw hφ')) _ hk
end

section

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp
open UpperTheory.V.Cj.S Formalism.UG.P
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)
open PositivityTheory.Rg.BcB.SpectralAccumulation (TypeB)

private theorem eigT_of {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {T : Set (UpperTheory.V.Cj.S.Pl E)} {K W}
    (φ : Sm E a) (h0 : φ ≠ 0) (haut : IsAutForm φ) (hty : TypeB K W φ) (hfix : ∀ w ∉ T, φ ∈ fixed (fL a w) (KGL w (n := a)))
    (l : Ix a T → ℂ) (hl : ∀ i, opIx i φ = l i • φ) :
    ∃ (m : (E →+* ℂ) → Multiset ℂ) (B : UpperTheory.V.Cj.S.Pl E → Multiset ℂˣ), EigT T K W φ m B ∧
      (∀ t u, l (.inl (t, u)) = ((m t).map (u + ·)).prod) ∧
      ∀ (w : UpperTheory.V.Cj.S.Pl E) (hw : w ∉ T) (ϖ : HeightOneSpectrum.adicCompletion E w) (hu : IsUnifV E w ϖ), ∀ j ≤ a,
        l (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩) = satEig (qV E w) a (B w) j := by
  classical
  obtain ⟨m, hm⟩ := capOfEig E a φ h0 fun t u => ⟨_, hl (.inl (t, u))⟩
  have hB : ∀ w : UpperTheory.V.Cj.S.Pl E, ∃ B : Multiset ℂˣ, w ∉ T → IsSatVecGL w (fL a w) φ B := by
    intro w
    by_cases hw : w ∈ T
    · exact ⟨0, fun h => (h hw).elim⟩
    · obtain ⟨B, hB⟩ := satOfEig E w a _ (fL a w) φ h0 (hfix w hw) fun h hh => ⟨_, hl (.inr ⟨⟨w, hw⟩, ⟨h, hh⟩⟩)⟩
      exact ⟨B, fun _ => hB⟩
  choose B hB using hB
  refine ⟨m, B, ⟨h0, haut, hty, hm, hB⟩, fun t u => ?_, fun w hw ϖ hu j hj => ?_⟩
  · exact smul_left_injective ℂ h0 ((hl (.inl (t, u))).symm.trans ((hm t).2 u))
  · exact smul_left_injective ℂ h0
      ((hl (.inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu j⟩⟩)).symm.trans ((hB w hw).2.2.2 ϖ hu j hj))

private def tySub {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (K : Subgroup (GL (Fin a) (Af E)))
    (W : Submodule ℂ (Kinf E a → ℂ)) : Submodule ℂ (Sm E a) where
  carrier := {φ | TypeB K W φ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  add_mem' h h' := ⟨fun u hu g => congrArg₂ (· + ·) (h.1 u hu g) (h'.1 u hu g), fun g => W.add_mem (h.2 g) (h'.2 g)⟩
  smul_mem' c _ h := ⟨fun u hu g => congrArg (c * ·) (h.1 u hu g), fun g => W.smul_mem c (h.2 g)⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.stepT :
    IwaT → SliceT → StabT → StepT := by
  intro hI hSl hSt E _ _ _ r s bad K W hK hW
  obtain ⟨K', W', hK', hW', hI⟩ := hI E r s bad K W hK hW
  obtain ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, hSl⟩ := hSl E r s bad K' W' hK' hW'
  refine ⟨K₁, W₁, K₂, W₂, l₁, f₁, l₂, f₂, fun φ₀ m B h₀ hne₀ => ?_⟩
  obtain ⟨φ, hφ, hne⟩ := hI φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := sliceBdd singleBdd E r s φ hφ.aut
  obtain ⟨t₁, t₂⟩ := hSl φ hφ.aut hφ.ty
  obtain ⟨V₁, a₁, fd₁, aut₁, fix₁, st₁⟩ := hSt E r bad K₁ W₁ l₁ f₁ (S₁ ⊓ tySub K₁ W₁)
    (hS₁.mono (Submodule.map_mono inf_le_left)) fun _ h => h.2
  obtain ⟨V₂, a₂, fd₂, aut₂, fix₂, st₂⟩ := hSt E s bad K₂ W₂ l₂ f₂ (S₂ ⊓ tySub K₂ W₂)
    (hS₂.mono (Submodule.map_mono inf_le_left)) fun _ h => h.2
  obtain ⟨ψ, hψ, hNI, hcap⟩ := ctCap E (r + s) r φ hφ.aut
  obtain ⟨φ₁, hφ₁, φ₂, hφ₂, e₁, e₂, n₁, n₂, g₁, g₂, H⟩ :=
    twoVar tensEigB _ _ (Sm E r) (Sm E s) V₁ V₂ fd₁ fd₂ (Ix r bad) (Ix s bad) opIx opIx st₁ st₂
      (fun i i' v hv => opComm capAct E r bad i i' v fun w hw => fix₁ w hw hv)
      (fun i i' v hv => opComm capAct E s bad i i' v fun w hw => fix₂ w hw hv) (res (constantTerm r φ.1)) hne
      (fun y => (hs₁ y).imp fun f hf => ⟨a₁ ⟨hf.1, t₁ y f hf.2⟩, hf.2⟩)
      (fun x => (hs₂ x).imp fun f hf => ⟨a₂ ⟨hf.1, t₂ x f hf.2⟩, hf.2⟩)
  rw [← hψ] at hne H
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨m₁, B₁, E₁, c₁, s₁⟩ := eigT_of φ₁ n₁ (aut₁ _ hφ₁).1 (aut₁ _ hφ₁).2 (fun w hw => fix₁ w hw hφ₁) e₁ g₁
  obtain ⟨m₂, B₂, E₂, c₂, s₂⟩ := eigT_of φ₂ n₂ (aut₂ _ hφ₂).1 (aut₂ _ hφ₂).2 (fun w hw => fix₂ w hw hφ₂) e₂ g₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, E₁, E₂, fun t => ?_, fun ν ν' hν hν' w hw => ?_⟩
  · refine capArith (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2, ← c₁, ← c₂]
    have := H Unit (fun _ => 1) (fun _ => .inl (t, _)) (fun _ => .inl (t, _)) (fun _ => _) ((m t).map (u + ·)).prod
      (fun _ => capRel slice capBlock E r s ψ hNI t u) fun x y => by
        rw [hcap t u, (hφ.cap t).2 u, hψ]
        simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.univ_unique, Finset.sum_singleton,
          one_mul]
        exact MeasureTheory.integral_const_mul _ _
    simpa using this
  · have hv := ctSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) (hφ.sat w hw)
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine satArith (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) (hφ.sat w hw).2.2.1 (E₁.sat w hw).2.2.1 (E₂.sat w hw).2.2.1
      (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hkRel slice hkSum (hkLocal sumInner matBlock) gl2_local_to_adelic_embedding E r s ψ hNI w hv.2.1 ϖ hu j hj
      have := H (Fin (r + 1) × Fin (s + 1)) _ (fun p => .inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu p.1⟩⟩)
        (fun p => .inr ⟨⟨w, hw⟩, ⟨_, Tj_mem_hecke hu p.2⟩⟩) G (satEig (qV E w) (r + s) (B w) j) hG fun x y => by
          rw [hsum x y]
          have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
          rw [this]
          rfl
      rw [← this]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [s₁ w hw ϖ hu p.1 (Nat.lt_succ_iff.1 p.1.2), s₂ w hw ϖ hu p.2 (Nat.lt_succ_iff.1 p.2.2)]
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end
