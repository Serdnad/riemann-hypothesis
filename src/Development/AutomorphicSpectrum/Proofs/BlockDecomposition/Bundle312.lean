module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle128
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle703
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.LocalFields.PadicLogSeries
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle123
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle298
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_between {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {U : Subgroup (GL (Fin N) k)}
    (hU : U ≤ unipB k (Fin N)) (hcl : IsClosed (U : Set (GL (Fin N) k)))
    (Q : Set (GL (Fin N) k)) (hQ : IsCompact Q) (hQU : Q ⊆ (U : Set (GL (Fin N) k))) :
    ∃ L : {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U},
      Q ⊆ (L.1 : Set (GL (Fin N) k)) := by
  have hQU' : Q ⊆ (unipB k (Fin N) : Set (GL (Fin N) k)) := fun g hg => hU (hQU hg)
  have hbase : ∃ U₀ : Subgroup (GL (Fin N) k), IsCompact (U₀ : Set (GL (Fin N) k)) ∧ Q ⊆ (U₀ : Set (GL (Fin N) k)) := by
    set c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
    have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
      ext g
      rw [mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
      constructor
      · rintro ⟨h1, h2⟩ i j hij
        have hji : j ≤ i := by
          dsimp [c] at hij
          rw [not_lt] at hij
          exact Fin.le_def.2 (by exact_mod_cast hij)
        rcases hji.lt_or_eq with h | h
        · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
        · subst h; rw [h2 j, Matrix.one_apply_eq]
      · intro h
        refine ⟨fun i j hji => ?_, fun i => ?_⟩
        · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
            have := Fin.lt_def.1 hji
            omega
          rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
        · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
    rw [heq] at hQU'
    let V : ℕ → Set (GL (Fin N) k) := fun m =>
      (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
    have hVo : ∀ m, IsOpen (V m) := fun m =>
      (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
    have hVmono : Monotone V := by
      intro m M hmM g hg
      rcases hg with hg | hg
      · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
        · apply Or.inl
          have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
              (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
              ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
            intro x hx hd i j
            by_cases hij : c i < c j
            · refine (hd i j).mono ?_
              have : (m : ℤ) ≤ M := by exact_mod_cast hmM
              nlinarith
            · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
              by_cases e : i = j
              · subst e
                simp [GlobalTheory.IwahoriInj.deep_zero_iff]
              · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
          exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
        · exact Or.inr hu
      · exact Or.inr hg
    have hcov : Q ⊆ ⋃ m, V m := fun g hg =>
      Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU' hg)).exists).imp fun _ h => Or.inl h)
    obtain ⟨M, hM⟩ := hQ.elim_directed_cover V hVo hcov hVmono.directed_le
    refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ GlobalTheory.InertSupp.unipOf k c, ?_, fun g hg => ?_⟩
    · rw [Subgroup.coe_inf]
      exact (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right (GlobalTheory.UnipCompact.isClosed_unipOf c)
    · rcases hM hg with h | h
      · exact ⟨h, hQU' hg⟩
      · exact absurd (hQU' hg) h
  obtain ⟨U₀, hc, hs⟩ := hbase
  refine ⟨⟨U₀ ⊓ U, ?_, inf_le_right⟩, fun g hg => ⟨hs hg, hQU hg⟩⟩
  rw [Subgroup.coe_inf]
  exact hc.inter_right hcl

theorem exists_monotone_compact_exhaustion :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (U : Subgroup (GL (Fin N) k)), U ≤ unipB k (Fin N) → IsClosed (U : Set (GL (Fin N) k)) →
      ∃ L : ℕ → Subgroup (GL (Fin N) k), Monotone L ∧ (∀ j, IsCompact (L j : Set (GL (Fin N) k))) ∧
        (∀ j, L j ≤ U) ∧ ∀ n ∈ U, ∃ j, n ∈ L j := by
  intro k _ _ _ _ N U hU hcl
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  haveI : SigmaCompactSpace (GL (Fin N) k) := inferInstance
  let S := {L : Subgroup (GL (Fin N) k) // IsCompact (L : Set (GL (Fin N) k)) ∧ L ≤ U}
  let K : ℕ → Set (GL (Fin N) k) := compactCovering (GL (Fin N) k)
  have hstep : ∀ (j : ℕ) (A : S), ∃ B : S,
      (K j ∩ (U : Set (GL (Fin N) k))) ∪ (A.1 : Set (GL (Fin N) k)) ⊆ (B.1 : Set (GL (Fin N) k)) :=
    fun j A => exists_compact_subgroup_between hU hcl _
      (((isCompact_compactCovering _ j).inter_right hcl).union A.2.1)
      (Set.union_subset Set.inter_subset_right A.2.2)
  choose next hnext using hstep
  let b : S := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, bot_le⟩
  let f : ℕ → S := fun j => Nat.rec b (fun i A => next i A) j
  have hsucc : ∀ j, f (j + 1) = next j (f j) := fun _ => rfl
  refine ⟨fun j => (f j).1, monotone_nat_of_le_succ fun j g hg => ?_, fun j => (f j).2.1,
    fun j => (f j).2.2, fun n hn => ?_⟩
  · rw [hsucc]
    exact hnext j (f j) (Or.inr hg)
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1
      ((iUnion_compactCovering (GL (Fin N) k)).symm ▸ Set.mem_univ n : n ∈ ⋃ i, K i)
    refine ⟨j + 1, ?_⟩
    show n ∈ (f (j + 1)).1
    rw [hsucc]
    exact hnext j (f j) (Or.inl ⟨hj, hn⟩)

end GlobalTheory.CompanionTheory.UnipExhaust
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  let c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
    ext g
    rw [GlobalTheory.SmGL.mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
    constructor
    · rintro ⟨h1, h2⟩ i j hij
      have hji : j ≤ i := by
        dsimp [c] at hij
        rw [not_lt] at hij
        exact Fin.le_def.2 (by exact_mod_cast hij)
      rcases hji.lt_or_eq with h | h
      · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h; rw [h2 j, Matrix.one_apply_eq]
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
          have := Fin.lt_def.1 hji
          omega
        rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
      · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
  have hQU : (↑s : Set (GL (Fin N) k)) ⊆ GlobalTheory.InertSupp.unipOf k c := by
    simpa [← heq] using hs
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
      · left
        have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
            (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
            ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
          intro x hx hd i j
          by_cases hij : c i < c j
          · refine (hd i j).mono ?_
            have : (m : ℤ) ≤ M := by exact_mod_cast hmM
            nlinarith
          · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
            by_cases e : i = j
            · subst e
              simp [GlobalTheory.IwahoriInj.deep_zero_iff]
            · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
        exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : (↑s : Set (GL (Fin N) k)) ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := s.finite_toSet.isCompact.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipB k (Fin N), inf_le_right, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, hs hg⟩
    rcases hM hg with h | h
    · exact h
    · exact absurd (hQU hg) h
  · rw [Subgroup.coe_inf]
    apply (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right
    rw [heq]
    exact GlobalTheory.UnipCompact.isClosed_unipOf _

end GlobalTheory.CompanionTheory.UnipExhaust
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HighestDeriv

section Coinv

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Coinv

def piFinTwoTensor (X : Fin 2 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] X 0 ⊗[ℂ] X 1 :=
  ((LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => X i.succ) 0).symm).trans
    (GlobalTheory.SmGL.MultiIrr.tensorCons X)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Two

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t : ℕ}

def piTensorTwoEquiv' (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  .mk (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)
        (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g)
        (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g) (x false) (x true)).symm

theorem nonempty_prod2_equiv (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod2 (k := k) rfl π₁ π₂).Equiv (prod₂ π₁ π₂)) :=
  ⟨LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv' π₁ π₂)⟩

end Two

section Main

end Main

end GlobalTheory.CompanionTheory.HighestDeriv

end
end

section

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
end
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def uM (n : ℕ) (x : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd x)

def shearGL (n : ℕ) (b : Fin (n + 1) → k) : GL (Fin (n + 1)) k :=
  open Classical in if h : IsUnit (1 + vecMulVec (eLast k n) b) then h.unit else 1

def piHaar [MeasurableSpace k] (ν : Measure k) (m : ℕ) : Measure (Fin m → k) := Measure.pi fun _ => ν

def wt (ψ : AddChar k Circle) (n : ℕ) (x : Fin (n + 1) → k) : ℂ := ((ψ (-x (Fin.last n)) : Circle) : ℂ)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (x : Fin n → k) : ℂ :=
  B (T (uM n x) v) v'

def TwInv (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) : Prop :=
  ∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
    ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v'

def JJ [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') : ℂ :=
  ∫ x in M, wt ψ n x * coef T B v v' x ∂(piHaar ν (n + 1))

def EvVal [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (A : ℂ) : Prop :=
  ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) →
    JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' = A

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_left : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_r | exact GlobalTheory.CompanionTheory.KunGlue.glue_r | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_r <;> assumption)
end
