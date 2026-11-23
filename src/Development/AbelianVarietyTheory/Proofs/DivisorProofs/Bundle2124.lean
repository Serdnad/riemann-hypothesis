module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
public import Formalism.PieriBlockIdeals.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Columns.Bundle031
public import Formalism.LocalToGlobal.Divisibility.BrJoint
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumOfHeisenbergLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacua
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealLineBlockEmbeddingExpInfinitePlace
public import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairLocal

theorem finLocal : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  have hLlat : Submodule.IsFullLattice E L := by
    haveI : Submodule.IsLattice E L := GlobalTheory.T.isLattice_of_lastCoordinate_extension hN M L hM.toIsLattice hL
    refine ⟨?_⟩
    subst hN
    have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
    have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
    simp only [hiC, hiL] at hL
    let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
      { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
        map_add' := by intro x y; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
        map_smul' := by intro a x; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
    let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
    have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [g] using hm, 0, by simp [g]⟩
    have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
    have hg : ∀ x : Fin n → E, g x ∈ Submodule.span E (L : Set (Fin (n + 1) → E)) := by
      intro x
      have hx : x ∈ Submodule.span E (M : Set (Fin n → E)) := by rw [hM.span_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (gm x hx)
      | zero => simp
      | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa using Submodule.smul_mem _ a ih
    apply top_unique
    intro x _
    have dec : x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
      ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [g, e, Pi.single_apply, Fin.castSucc_ne_last]
    rw [dec]
    exact Submodule.add_mem _ (hg _) (Submodule.smul_mem _ _ (Submodule.subset_span he))
  have h1 := GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr E K ι N emb Λ L hLlat w u hu
  obtain ⟨s, hs, hsu⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h1
  have hdel : delAtr emb Λ L = delK Λ (fun τ => Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) (1 : K)) := by
    unfold delAtr
    congr 1
    funext τ
    exact GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum emb hN M L hL τ
  rw [hdel] at hsu
  have h2 := GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs K ι N n hN Λ σ hI hS
    (fun τ => dualFr (tauLat emb τ M)) (fun _ => 1) (fun _ => one_ne_zero) _ hsu
  have hbr : Formalism.L2.Col.Br.brAt hN Λ σ (fun _ => (1 : K)) = Formalism.L2.Col.Br.brStd hN Λ σ := by
    simp [Formalism.L2.Col.Br.brAt]
  rw [hbr] at h2
  have hy := GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla emb σ M hM.toIsLattice v hv
  have h3 := ((Formalism.L2.DIV.pairBDual E K ι n emb σ M hM _).1.1 h2) _ hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
  have key : (s : K) * (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) *
      GlobalTheory.BrPairF.brPairF σ hN Λ u v = (r : K) := by
    have e1 : (r : K) = algebraMap (𝓞 K) K r := rfl
    rw [e1, hr, GlobalTheory.BrPairF.brPairF_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_natCast, mul_assoc]
  by_cases hP : GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0
  · exact Or.inl hP
  right
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact w.asIdeal.zero_mem
  have hp0 : (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Formalism.EigenvalueLevelCeiling.plc_prime w).ne_zero)
  have h4 := Formalism.DivisionValues.ReductionFirst.vw_int_nonneg w r
  rw [← key, Formalism.DivisionValues.ReductionFirst.vw_mul w (mul_ne_zero hs0 hp0) hP, Formalism.DivisionValues.ReductionFirst.vw_mul w hs0 hp0,
    Formalism.DivisionValues.ReductionFirst.vw_unit w s hs] at h4
  linarith

end GlobalTheory.BrPairLocal
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacUniq

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem schr_schr {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → K) × (κ → K)) (φ : (κ → K) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  have key : (x ⬝ᵥ w.2 + ⅟(2 : K) * (w.1 ⬝ᵥ w.2)) + ((x + w.1) ⬝ᵥ w'.2 + ⅟(2 : K) * (w'.1 ⬝ᵥ w'.2)) =
      ⅟(2 : K) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) +
        (x ⬝ᵥ (w + w').2 + ⅟(2 : K) * ((w + w').1 ⬝ᵥ (w + w').2)) := by
    have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
    linear_combination (-(w.1 ⬝ᵥ w'.2)) * h2
  show ψ _ * (ψ _ * φ (x + w.1 + w'.1)) = ψ _ * (ψ _ * φ (x + (w + w').1))
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]

theorem acts_unique {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {κ : Type} [Fintype κ] {φ : (κ → Fv F v) → ℂ}
    {r : (κ → AF F) → ℂ} (hr : Rest (evFin F v) φ r) {x₀ : κ → AF F} (hx₀ : r x₀ ≠ 0)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i)) with hz
  have hza : At (evFin F v) z := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hrx : r (x₀ + z) = r x₀ := hr.1 x₀ z hza
  have hy : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [hz, Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV, add_sub_cancel]
  have e := congrFun ((h1 r hr).symm.trans (h2 r hr)) (x₀ + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hx₀ e

theorem phase {V : Type} [AddCommGroup V] [Module ℂ V] {φ ψ S : V} {c χ : ℂ} (hne : φ ≠ 0)
    (h1 : φ = (c * χ) • φ) (h2 : ψ = c • S) : S = χ • ψ := by
  have hcχ : c * χ = 1 := by
    by_contra hne'
    have h4 : (c * χ - 1) • φ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact hne ((smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne'))
  rw [h2, smul_smul, mul_comm, hcχ, one_smul]

theorem sa_bd_uniq : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ)) (hι : Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∀ g ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)), (∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, g (Y + s) = g Y) →
      (∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, g Y = 0) → ∃ c : ℂ, g = c • ι φ₀ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq g hg hSa hBd
  have hψc : Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) := GlobalTheory.VacAny.continuous_psiV hTr.base.std.1 Bs.v₁
  have hSB : ∀ γ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁),
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ ∈ GlobalTheory.WeilM.SB _ :=
    fun γ φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB _ _ hψc _ _ hφ
  have hat : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, At (evFin D.host.F Bs.v₁) γ :=
    (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1
  have hacts : ∀ γ, At (evFin D.host.F Bs.v₁) γ → ∀ φ, Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ
      (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) :=
    fun γ hγ φ => GlobalTheory.VacBridge.rho_acts_locCo Γ.M'.co Bs.ψ Bs.v₁ γ hγ φ
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.T.exists_nonzero_complementary_adelicSchwartz_function Bs.v₁ φ₀ h0
  obtain ⟨χ, hχ⟩ : ∃ χ : Matrix (Fin a') (Fin (a + a')) (AE D.host.F D.host.E) → ℂ, ∀ γ, χ γ =
      Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
        (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) := ⟨_, fun _ => rfl⟩
  have hφ₀ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ₀ = χ γ • φ₀ := by
    intro γ hγ
    rw [hχ]
    exact acts_unique Bs.v₁ hr hx₀ _ _ _ (hacts γ (hat γ hγ) φ₀) (hfix γ hγ)
  have hχ1 : ∀ u, At (evFin D.host.F Bs.v₁) u →
      (u.map (piW Bs.τ₁) = 0 ∨ u.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0) → χ u = 1 := by
    intro u hu h
    rw [hχ, GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hu h, mul_zero, AddChar.map_zero_eq_one]
  obtain ⟨ψ₀, hψ₀, hιψ₀⟩ := hι.bij.surjOn hg
  have hA : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁, γ.map (piW Bs.τ₁) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    have ht : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) Y =
        ι ψ₀ (Y + GlobalTheory.VacShape.coBar Bs Γ γ) :=
      hι.trans γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) Y
    have hs : GlobalTheory.VacShape.coBar Bs Γ γ ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ := ⟨γ, hγ, h, rfl⟩
    rw [ht, hιψ₀]
    exact hSa _ hs Y
  have hB : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      γ.map (piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 →
      schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀ = ψ₀ := by
    intro γ hγ h
    refine hι.bij.injOn (hSB γ ψ₀ hψ₀) hψ₀ ?_
    funext Y
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_splitSupported_oppositeLagrangian_coordinate Bs Γ X om om' hTr Y
    have hm : ι (schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) ψ₀) (GlobalTheory.VacShape.coBar Bs Γ x) =
        Bs.ψ (symp (cA D.sp.cm.sig) (-1) (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) x γ) *
          ι ψ₀ (GlobalTheory.VacShape.coBar Bs Γ x) :=
      hι.mult γ (hat γ hγ) h ψ₀ hψ₀ _ (hSB γ ψ₀ hψ₀) (hacts γ (hat γ hγ) ψ₀) x hx hx0
    rw [hm, hιψ₀]
    by_cases hY : GlobalTheory.VacShape.coBar Bs Γ x ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂
    · rw [hY x hx hx0 rfl γ hγ h, one_mul]
    · rw [hBd _ hY, mul_zero]
  have hfixψ : ∀ γ ∈ latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
        (Bs.ψ (⅟(2 : AF D.host.F) * symp (cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
          (incM D.host.F Γ.V'.J) (incM D.host.F Γ.W.J) γ γ) • ψ₀) := by
    intro γ hγ
    rw [← hχ]
    obtain ⟨γA, hγA, γB, hγB, rfl, hA0, hB0⟩ := GlobalTheory.T.tensorLatticeSplitPlace_eq_add_componentParts Bs Γ X om om' hTr L₁ L₂ γ hγ
    have e0 : GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (γA + γB) =
        GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA + GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB := map_add _ _ _
    have hc := schr_schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA)
      (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB)
    have hφA : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γA) φ₀ = φ₀ := by
      rw [hφ₀ γA hγA, hχ1 γA (hat γA hγA) (Or.inl hA0), one_smul]
    have hφB : schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γB) φ₀ = φ₀ := by
      rw [hφ₀ γB hγB, hχ1 γB (hat γB hγB) (Or.inr hB0), one_smul]
    have h1 := hc φ₀
    rw [hφB, hφA, ← e0, hφ₀ _ hγ, smul_smul] at h1
    have h2 := hc ψ₀
    rw [hB γB hγB hB0, hA γA hγA hA0, ← e0] at h2
    have key := phase hne h1 h2
    have := hacts _ (hat _ hγ) ψ₀
    rwa [key] at this
  obtain ⟨c, hc⟩ := huniq ψ₀ hψ₀ hfixψ
  exact ⟨c, by rw [← hιψ₀, hc, map_smul]⟩

end GlobalTheory.VacUniq

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


theorem _root_.GlobalTheory.T.exists_finitePlaceVacuum_of_heisenbergLattice : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), Continuous ψ → GlobalTheory.LatVac.psiAt ψ v ≠ 1 →
    ∀ Γ : AddSubgroup W, (∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ γ ∈ Γ, GlobalTheory.LatVac.liftV v a • γ ∈ Γ) →
    IsOpen ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    IsCompact ((Γ.map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
    ∀ c : W → ℂ, c 0 = 1 → (∀ γ ∈ Γ, ∀ γ' ∈ Γ, c (γ + γ') = c γ * c γ' * ψ (⅟(2 : AF F) * B γ γ')) →
    (∀ γ ∈ Γ, c (GlobalTheory.LatVac.liftV v 2 • γ) = 1) →
    ∃ φ : (κ → Fv F v) → ℂ, φ ∈ GlobalTheory.WeilM.SB _ ∧ φ ≠ 0 ∧
      ∀ γ ∈ Γ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ (c γ • φ) := by
  first | exact @GlobalTheory.HeisLatVac.exists_vac_of_lattice | exact GlobalTheory.HeisLatVac.exists_vac_of_lattice | (intros; apply GlobalTheory.HeisLatVac.exists_vac_of_lattice <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  first | exact @GlobalTheory.OffVTrig.exists_offV_indicator_poly | exact GlobalTheory.OffVTrig.exists_offV_indicator_poly | (intros; apply GlobalTheory.OffVTrig.exists_offV_indicator_poly <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat


theorem _root_.GlobalTheory.T.heisenbergStableRelation_of_vacua : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  first | exact @GlobalTheory.InductLagr.rel_of_vac | exact GlobalTheory.InductLagr.rel_of_vac | (intros; apply GlobalTheory.InductLagr.rel_of_vac <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_blockProjection_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  first | exact @GlobalTheory.BlockForms.Proj.exists_blockProj | exact GlobalTheory.BlockForms.Proj.exists_blockProj | (intros; apply GlobalTheory.BlockForms.Proj.exists_blockProj <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.blockEmbedding_rationalGL_mem_rationalPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  first | exact @GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | exact GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts | (intros; apply GlobalTheory.CuspBlockRat.blockEmb_ratGL_mem_ratPts <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ContDiff

theorem _root_.GlobalTheory.T.isRealLine_blockEmbedding_exp_infinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
    ∀ (v : InfinitePlace E) (X : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i j, ∀ u, u ≠ v → X i j u = 0) →
      IsRealLine σ J fun t : ℝ => ι (GlobalTheory.CuspRep.infGL E d (GlobalTheory.CuspRep.expGLi d (t • X))) := by
  first | exact @GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp | exact GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp | (intros; apply GlobalTheory.BlockRealLine.isRealLine_blockEmb_exp <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.blockEmbedding_unipotent_mem_flagUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∀ x : GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E, ι (GlobalTheory.CuspRep.unip x) ∈ GlobalTheory.StdPar.unip σ J Xf (insert k S) := by
  first | exact @GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem | exact GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem | (intros; apply GlobalTheory.BlockForms.CuspUnip.blockEmb_unip_mem <;> assumption)
end
