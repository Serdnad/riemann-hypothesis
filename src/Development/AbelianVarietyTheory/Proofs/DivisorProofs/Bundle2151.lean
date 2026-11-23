module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairLocalZetaMatchNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertVacLagP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_map_compFin (v : Pl (F := F)) {d m : ℕ} (Cy : Matrix (Fin d) (Fin m) (Fv F v ⊗[F] E)) :
    ∃ C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), C.map (compFin F E v) = Cy := by
  have hs : Function.Surjective (compFin F E v) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul x e =>
      refine ⟨GlobalTheory.LatVac.liftV v x ⊗ₜ e, ?_⟩
      simp [compFin, GlobalTheory.LatVac.evFin_liftV]
    | add x y hx hy =>
      obtain ⟨p, hp⟩ := hx
      obtain ⟨q, hq⟩ := hy
      exact ⟨p + q, by rw [map_add (f := _), hp, hq]⟩
  choose f hf using hs
  exact ⟨Cy.map f, by ext i j; simp [hf]⟩

def lagSub {n d m : ℕ} (v : Pl (F := F)) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : AddSubgroup (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) where
  carrier := GlobalTheory.InertVacLag.lagAt v C
  zero_mem' := ⟨fun u _ => smul_zero u, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨hx, z, rfl⟩ ⟨hy, z', rfl⟩
    exact ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩
  neg_mem' := by
    rintro x ⟨hx, z, rfl⟩
    exact ⟨fun u hu => by rw [smul_neg, hx u hu, neg_zero], -z, by rw [Matrix.neg_mul]⟩

theorem acts_unique {κ : Type} [Fintype κ] (v : Pl (F := F)) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (φ φ₁ φ₂ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v)) (h1 : Acts (evFin F v) T φ φ₁)
    (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have e := (h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ))
  funext y
  have hy := congrFun e (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens] at hy
  have hev : (fun i => evFin F v (GlobalTheory.LatVac.liftV v (y i))) = y := funext fun i => GlobalTheory.LatVac.evFin_liftV v (y i)
  rw [hev] at hy
  have hRx : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    have := (hR φ hφ).1 0 (fun i => GlobalTheory.LatVac.liftV v (y i)) (fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu)
    simpa using this
  rw [hRx] at hy
  exact mul_right_cancel₀ hR0 hy

theorem eq_of_locCo {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (co : Darboux Bf κ) (v : Pl (F := F)) (g u : W) (hg : At (evFin F v) g) (hu : At (evFin F v) u)
    (h : GlobalTheory.LatVac.locCo co v g = GlobalTheory.LatVac.locCo co v u) : g = u := by
  have hA : ∀ z : W, At (evFin F v) z → ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) := by
    intro z hz k
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := congrArg (fun p => p.1 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
    · have := congrArg (fun p => p.2 k) (show co.e (t • z) = t • co.e z from co.e.map_smul t z)
      simpa [hz t ht] using this.symm
  apply co.e.injective
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).1, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).1]
    exact congrArg _ (congrFun h1 k)
  · rw [GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA g hg k).2, GlobalTheory.VacAny.eq_atPlace_of_at v _ (hA u hu k).2]
    exact congrArg _ (congrFun h2 k)

theorem exists_lagr_inv_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∃ (C : Matrix (Fin (a + a')) (Fin ((a + a') / 2)) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (l : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      GlobalTheory.InertVacLag.IsLagrAt σ G.W v C ∧ GlobalTheory.InertVacLag.HeisInv G.M' B.ψ v C l ∧ l (G.M'.vac v) ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin _
  obtain ⟨Cy, hCy⟩ := GlobalTheory.InertLagr.exists_lagr F E σ B a a' G X om om' hT v w hin
  obtain ⟨C, hC⟩ := exists_map_compFin (E := E) v Cy
  have hLag : GlobalTheory.InertVacLag.IsLagrAt σ G.W v C := by
    unfold GlobalTheory.InertVacLag.IsLagrAt; rw [hC]; exact hCy
  set co := G.M'.co with hco
  set Λ := (lagSub (n := a') v C).map (GlobalTheory.LatVac.locCo co v) with hΛ
  set Γ := (latAtV G.V' G.W v).map (GlobalTheory.LatVac.locCo co v) with hΓ
  have hgood := hT.base.inert v w hin
  obtain ⟨hsb, hne, θ, hθ, hvac⟩ := hT.geo.hM'.vac v
  have hatL := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := hT.base.std.1.comp (GlobalTheory.VacAny.continuous_atPlace v)
  have hψ : ∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, GlobalTheory.LatVac.psiAt B.ψ v (x * y) = 1) →
      x ∈ v.adicCompletionIntegers F := fun x hx => (hgood.2.2 x).1 hx
  have hiso : ∀ x ∈ Λ, ∀ x' ∈ Λ, x.1 ⬝ᵥ x'.2 - x'.1 ⬝ᵥ x.2 = 0 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
    have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag (-1) u u' hu hu'
    change symp (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) u u' = 0 at h0
    rw [co.form] at h0
    have h1 := congrArg (evFin F v) h0

    simpa [GlobalTheory.LatVac.locCo, dotProduct, map_sum, map_mul, map_sub] using h1
  have hOC := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat v
  have hdual := GlobalTheory.LatVac.DualLoc.map_selfDual v co B.ψ (latAtV G.V' G.W v) hatL
    (GlobalTheory.T.inertPlace_tensorLattice_selfDual_supportedAt F E σ B a a' G X om om' hT v w hin)
  have heig0 : ∀ g ∈ latAtV G.V' G.W v, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo co v g) (G.M'.vac v) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) g g) • G.M'.vac v :=
    fun g hg => acts_unique v _ _ _ _ hsb (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v g (hatL g hg) _) (hvac g hg)
  have heig : ∀ γ ∈ Γ, ∃ c : ℂ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = c • G.M'.vac v := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨_, heig0 g hg⟩
  have hfix : ∀ γ ∈ Γ ⊓ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) γ (G.M'.vac v) = G.M'.vac v := by
    rintro γ ⟨⟨g, hg, rfl⟩, ⟨u, hu, hgu⟩⟩
    have e : g = u := eq_of_locCo co v g u (hatL g hg) hu.1 hgu.symm
    subst e
    rw [heig0 g hg, GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ G.V'.J G.W v C hLag _ g g hu hu, mul_zero, AddChar.map_zero_eq_one, one_smul]
  obtain ⟨l, hl, hl0⟩ := GlobalTheory.T.lagrangian_invariant_linearForm_local_uniqueness v (GlobalTheory.LatVac.psiAt B.ψ v) (Fin a' × Fin (a + a')) Λ Γ (G.M'.vac v) hψc hψ hiso
    hOC.1 hOC.2 hdual hsb hne heig hfix
  refine ⟨C, l, hLag, ?_, hl0⟩
  intro u hu φ hφ φ₁ _ hA
  have e := acts_unique v _ φ φ₁ _ hφ hA (GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v u hu.1 φ)
  rw [e]
  exact hl _ ⟨u, hu, rfl⟩ φ hφ

end GlobalTheory.InertVacLagP

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

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem GlobalTheory.LinModelLocal.exists_omB_of_linBar : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, S g (c • φ + φ') = c • S g φ + S g φ') →
    (∀ g g', ∀ φ ∈ GlobalTheory.WeilM.SB _, S (g * g') φ = S g (S g' φ)) →
    (∀ φ ∈ GlobalTheory.WeilM.SB _, S 1 φ = φ) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin a' × Fin (a + a') → Fv F Bs.v₁) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∃ ν α : (Fv F Bs.v₁)ˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧
      ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι → ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = omB ν α g 1 (ι φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr K hK S h1 hlin h2 h3 h4 h5
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char Bs Γ X om om' hTr K hK S h1 h4
  by_cases hex : ∃ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι
  swap
  · exact ⟨1, 1, fun x => by simp, fun ι hι => absurd ⟨ι, hι⟩ hex⟩
  obtain ⟨ι₀, hι₀⟩ := hex
  obtain ⟨hT0, hM0, hST0, hSM0⟩ := hA ι₀ hι₀
  have hbij0 := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.IsLin.bij hι₀
  have hU0 : ∀ (w : (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁), GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) w φ ∈ GlobalTheory.WeilM.SB _ :=
    fun w => GlobalTheory.T.schroedingerOperatorHeisenberg_preserves_schwartzBruhat (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc w
  have key1 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      h.valᵀ * (((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.one_mul]
  have key2 : ∀ (h : GL (Fin a') (Fv F Bs.v₁)) (Y : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁)),
      ((h⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * (h.valᵀ * Y) = Y := by
    intro h Y
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
  have hc : ∀ g : GL (Fin a') (Fv F Bs.v₁), ∃ c : ℂ, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      (fun Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) = c • ι₀ φ := by
    intro g
    refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
      (fun φ Y => ι₀ (S g φ) (((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y)) hbij0 ?_
      (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
      (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l)) ?_ ?_
    · intro x hx y hy c
      funext Y
      simp only [hlin g x hx y hy c, map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply]
    · intro C x hx
      refine ⟨hU0 _ x hx, hT0 C x hx, ?_⟩
      funext Y
      simp only [hST0 g C x hx, Matrix.mul_add]
    · intro l x hx
      refine ⟨hU0 _ x hx, hM0 l x hx, ?_⟩
      funext Y
      simp only [hSM0 g l x hx, key1]
  choose c hc using hc
  have hrel : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁),
      ι₀ (S g φ) = fun Y => c g * ι₀ φ (g.valᵀ * Y) := by
    intro g φ hφ
    funext Y
    have := congrFun (hc g φ hφ) (g.valᵀ * Y)
    simp only [key2, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hvac := (hTr.geo.hM'.vac Bs.v₁)
  set φv := Γ.M'.vac Bs.v₁
  have hφv : φv ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁) := hvac.1
  have hιv : ι₀ φv ≠ 0 := by
    intro h0
    exact hvac.2.1 (hbij0.injOn hφv (Submodule.zero_mem _) (by rw [h0, map_zero]))
  obtain ⟨Y₀, hY₀⟩ := Function.ne_iff.mp hιv
  have hmul : ∀ g g', c (g * g') = c g * c g' := by
    intro g g'
    have e := congrFun (congrArg ι₀ (h2 g g' φv hφv)) ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)
    rw [hrel (g * g') φv hφv, hrel g (S g' φv) (h1 g' φv hφv), hrel g' φv hφv] at e
    beta_reduce at e
    have e2 : (g'.val)ᵀ * ((g.val)ᵀ * ((((g * g')⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * Y₀)) = Y₀ := by
      rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, key1]
    rw [key1 (g * g') Y₀, e2] at e
    exact mul_right_cancel₀ hY₀ (e.trans (mul_assoc _ _ _).symm)
  have hone : c 1 = 1 := by
    have e := congrFun (congrArg ι₀ (h3 φv hφv)) Y₀
    rw [hrel _ _ hφv] at e
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul] at e
    exact (mul_eq_right₀ hY₀).mp e
  let cH : GL (Fin a') (Fv F Bs.v₁) →* ℂ := ⟨⟨c, hone⟩, hmul⟩
  have h2ne : (2 : Fv F Bs.v₁) ≠ 0 := (isUnit_of_invertible (2 : Fv F Bs.v₁)).ne_zero
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero h2ne cH.toHomUnits
  have hcχ : ∀ g, c g = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) := fun g => by
    rw [← hχ g]; rfl
  obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.abs_weilCharacter_det_eq_abs_det_pow (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀ hbij0
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C φ hφ => ⟨hU0 _ φ hφ, hT0 C φ hφ⟩) (fun l φ hφ => ⟨hU0 _ φ hφ, hM0 l φ hφ⟩)
    (fun μ hμ C φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ') (fun μ hμ l φ _ φ' _ => GlobalTheory.T.schroedingerOperatorHeisenberg_inner_preserving _ hψc μ hμ _ φ φ')
    S h1 h5 χ (fun g φ hφ => by rw [hrel g φ hφ, hcχ g])
  refine ⟨ν, 1, hν1, ?_⟩
  intro ι hι g φ hφ
  obtain ⟨hT, hM, -, -⟩ := hA ι hι
  obtain ⟨c', hc'⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F Bs.v₁)) (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) hψc hψ1 ι₀
    ι hbij0 (fun x _ y _ c => by rw [map_add (f := _), map_smul])
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l))
    (fun C x hx => ⟨hU0 _ x hx, hT0 C x hx, hT C x hx⟩) (fun l x hx => ⟨hU0 _ x hx, hM0 l x hx, hM l x hx⟩)
  rw [hc' _ (h1 g φ hφ), hc' φ hφ, hrel g φ hφ, hcχ g, hν g]
  funext Y
  simp only [omB, Pi.smul_apply, smul_eq_mul, map_one, Units.val_one, Matrix.mul_one, Fintype.card_fin, gdet,
    MonoidHom.one_apply, apow_one]
  push_cast
  ring
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.LocOpInv

theorem pure_mem {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = stdInd F κ v) : pure f φ ∈ schA F κ :=
  GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd

theorem stdInd_mem_SB_ne {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) :
    stdInd F κ v ∈ SB (κ → Fv F v) ∧ stdInd F κ v ≠ 0 := by
  refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [stdInd, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from fun i => zero_mem _)] at h0
  exact one_ne_zero h0

theorem isLocOp_inv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  classical
  intro F _ _ κ _ e he hbij
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  have hne : ∀ v, ev v (stdInd F κ v) ≠ 0 := fun v h =>
    (stdInd_mem_SB_ne v).2 (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v _ (stdInd_mem_SB_ne v).1 h)
  obtain ⟨S, hS⟩ := GlobalTheory.T.schwartz_bijection_right_inverse _ _ ei (GlobalTheory.T.bijective_infinite_part_of_restricted_product e ei ev hSB hstd hloc hbij hne)

  have hbv : ∀ v, Function.Bijective ((ev v).restrict (p := SB (κ → Fv F v)) (q := SB (κ → Fv F v)) (hSB v)) := by
    intro v
    refine ⟨?_, ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun ψ hψ => ?_
      exact Subtype.ext (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v ψ.1 ψ.2 (congrArg Subtype.val hψ))
    · intro χ
      obtain ⟨ψ, hψ, h⟩ := GlobalTheory.T.local_operators_product_compatible e ei ev hSB hstd hloc hbij.surjOn hne v χ.1 χ.2
      exact ⟨⟨ψ, hψ⟩, Subtype.ext h⟩
  let Lv : ∀ v, SB (κ → Fv F v) ≃ₗ[ℂ] SB (κ → Fv F v) := fun v => LinearEquiv.ofBijective _ (hbv v)
  have hCv : ∀ v, ∃ C : Submodule ℂ ((κ → Fv F v) → ℂ), IsCompl (SB (κ → Fv F v)) C := fun v =>
    Submodule.exists_isCompl _
  choose Cv hCv using hCv
  let ev' : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ ((Lv v).symm : SB (κ → Fv F v) →ₗ[ℂ] SB (κ → Fv F v)) ∘ₗ
      Submodule.linearProjOfIsCompl _ _ (hCv v)
  have hev'1 : ∀ v, ∀ ψ (hψ : ψ ∈ SB (κ → Fv F v)), ev' v ψ = ((Lv v).symm ⟨ψ, hψ⟩ : SB _) := by
    intro v ψ hψ
    simp only [ev', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ (hCv v) ψ = ⟨ψ, hψ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left (hCv v) ⟨ψ, hψ⟩
    rw [hp]
  have hev'SB : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev' v ψ ∈ SB (κ → Fv F v) := fun v ψ hψ => by
    rw [hev'1 v ψ hψ]; exact Subtype.property _
  have hevev' : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v (ev' v ψ) = ψ := by
    intro v ψ hψ
    rw [hev'1 v ψ hψ]
    have := congrArg Subtype.val ((Lv v).apply_symm_apply ⟨ψ, hψ⟩)
    exact this
  have hev'std : ∀ᶠ v in cofinite, ev' v (stdInd F κ v) = stdInd F κ v := by
    filter_upwards [hstd] with v hv
    have h1 := (stdInd_mem_SB_ne (κ := κ) v).1
    rw [hev'1 v _ h1]
    have : (Lv v) ⟨stdInd F κ v, h1⟩ = ⟨stdInd F κ v, h1⟩ := Subtype.ext hv
    rw [← this, LinearEquiv.symm_apply_apply]

  let Le : schA F κ ≃ₗ[ℂ] schA F κ := LinearEquiv.ofBijective ((e.restrict (p := schA F κ) (q := schA F κ)
    fun Φ hΦ => hbij.mapsTo hΦ)) ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, h⟩ := hbij.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (schA F κ)
  let e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    (schA F κ).subtype ∘ₗ (Le.symm : schA F κ →ₗ[ℂ] schA F κ) ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have he'e : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
    intro Φ hΦ
    have h1 : e Φ ∈ schA F κ := hbij.mapsTo hΦ
    simp only [e', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ hC (e Φ) = ⟨e Φ, h1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e Φ, h1⟩
    rw [hp]
    have : Le ⟨Φ, hΦ⟩ = ⟨e Φ, h1⟩ := rfl
    rw [← this, LinearEquiv.symm_apply_apply]
  refine ⟨e', ⟨S, ev', hev'SB, hev'std, fun f φ hφ hφs => ?_⟩, he'e⟩
  have hφ' : ∀ v, ev' v (φ v) ∈ SB (κ → Fv F v) := fun v => hev'SB v _ (hφ v)
  have hφ's : ∀ᶠ v in cofinite, ev' v (φ v) = stdInd F κ v := by
    filter_upwards [hφs, hev'std] with v h1 h2
    rw [h1, h2]
  have hΨ : pure (S f) (fun v => ev' v (φ v)) ∈ schA F κ := pure_mem (S f) _ hφ' hφ's
  have hE : e (pure (S f) fun v => ev' v (φ v)) = pure f φ := by
    rw [hloc _ _ hφ' hφ's, hS]
    congr 1
    funext v
    exact hevev' v _ (hφ v)
  rw [← hE, he'e _ hΨ]

end GlobalTheory.LocOpInv

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.standardPair_localZetaMatch_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c m a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → ν = α / β → 1 ≤ c → GlobalTheory.SplitFlip.CondLE ϖ c ν →
    GlobalTheory.SplitFlip.CondLE ϖ m α → GlobalTheory.SplitFlip.CondLE ϖ m β → (∀ x, ‖(α x : ℂ)‖ = 1) → (∀ x, ‖(β x : ℂ)‖ = 1) →
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') =
        GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') ∧
      GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') ≠ 0 := by
  first | exact @GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | exact GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB | (intros; apply GlobalTheory.StdPairMatch.bigZetaIntegral_stdA_eq_smallZetaIntegral_stdB <;> assumption)
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.weilDatum_doubleSpace_acts_unitScalar_seesaw_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ)),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : Formalism.IndefR.DatumF.GAF σ JT) (hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)),
        Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1, h) f₁) f₂ := by
  first | exact @PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | exact PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant | (intros; apply PositivityTheory.ThKW.weil_rep_unitary_pair_equivariant <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.oppositeKernelsRationalRowMap_largeConstants : BigC fun _ ch _ _ => RatRowAt ch := by
  first | exact @GlobalTheory.KerConjMean.ratRowAt_big | exact GlobalTheory.KerConjMean.ratRowAt_big | (intros; apply GlobalTheory.KerConjMean.ratRowAt_big <;> assumption)
end
