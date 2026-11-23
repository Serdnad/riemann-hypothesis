module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.AdelicSvN

variable {F : Type} [Field F] [NumberField F]

theorem dot_smul_rat {κ : Type} [Fintype κ] (s t : AF F) (u v : (κ → F) × (κ → F)) :
    (s • ((fun i => algebraMap F (AF F) (u.1 i)), (fun i => algebraMap F (AF F) (u.2 i)))).1 ⬝ᵥ
      (t • ((fun i => algebraMap F (AF F) (v.1 i)), (fun i => algebraMap F (AF F) (v.2 i)))).2 =
      s * t * algebraMap F (AF F) (u.1 ⬝ᵥ v.2) := by
  simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [show (fun i => algebraMap F (AF F) (u.1 i)) ⬝ᵥ (fun i => algebraMap F (AF F) (v.2 i)) =
    algebraMap F (AF F) (u.1 ⬝ᵥ v.2) from (RingHom.map_dotProduct (algebraMap F (AF F)) u.1 v.2).symm]
  ring

theorem inv_sum (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))) (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ)
    {ι : Type} (s : Finset ι) (t : ι → AF F) (w : ι → (κ → F) × (κ → F)) (hw : ∀ j, w j ∈ L) :
    ∀ φ ∈ schA F κ, l (schr ψ (∑ j ∈ s, t j • ((fun i => algebraMap F (AF F) ((w j).1 i)),
      (fun i => algebraMap F (AF F) ((w j).2 i)))) φ) = l φ := by
  classical
  induction s using Finset.induction_on with
  | empty => intro φ _; simp only [Finset.sum_empty]; congr 1; funext x; simp [schr]
  | insert j s hj ih =>
    intro φ hφ
    set a := t j • ((fun i => algebraMap F (AF F) ((w j).1 i)), (fun i => algebraMap F (AF F) ((w j).2 i)))
    set b := ∑ k ∈ s, t k • ((fun i => algebraMap F (AF F) ((w k).1 i)), (fun i => algebraMap F (AF F) ((w k).2 i)))
    have hab : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0 := by
      simp only [a, b, Prod.fst_sum, Prod.snd_sum, dotProduct_sum, sum_dotProduct, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [dot_smul_rat, dot_smul_rat, hL _ (hw j) _ (hw k)]
      ring
    have e := GlobalTheory.ThetaQuasiRat.schr_schr ψ a b φ
    rw [hab, mul_zero, AddChar.map_zero_eq_one, one_smul] at e
    rw [Finset.sum_insert hj, ← e, hl _ _ (hw j) _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ b φ hφ), ih φ hφ]

end GlobalTheory.AdelicSvN

namespace GlobalTheory.AdelicSvN
variable {F : Type} [Field F] [NumberField F]

theorem realised_of_mem_closure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (gens F κ)) : Realised ψ g := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_levi_inverseTranspose F ψ κ A hA
    · exact GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz F ψ hψ κ C hC
    · exact GlobalTheory.T.isRealisedOnAdelicSchwartz_weyl_fourier F ψ hψ κ
  | one => exact realised_one ψ
  | mul g h _ _ hg hh => exact hg.mul hh

theorem act_zero_eq_sum {κ : Type} [Fintype κ] [DecidableEq κ] (g : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (y : κ → AF F) :
    act g (0, y) = ∑ j, y j • ((fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inl) i)),
      (fun i => algebraMap F (AF F) (((g *ᵥ Sum.elim 0 (Pi.single j 1)) ∘ Sum.inr) i))) := by
  have key : ∀ k, (g.map (algebraMap F (AF F)) *ᵥ Sum.elim 0 y) k =
      ∑ j, y j * algebraMap F (AF F) ((g *ᵥ Sum.elim 0 (Pi.single j 1)) k) := by
    intro k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, Matrix.map_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j (fun m _ hm => by simp [Pi.single_apply, hm]) (by simp)]
    simp [mul_comm]
  ext i
  · simp only [act, Function.comp_apply, key, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  · simp only [act, Function.comp_apply, key, Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F))), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) →
    Module.finrank F L = Fintype.card κ →
    ∀ l₁ ∈ (adeleClass F).adm κ, ∀ l₂ ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₁ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₁ φ) →
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l₂ (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l₂ φ) →
    (∃ φ ∈ schA F κ, l₂ φ ≠ 0) → ∃ c : ℂ, ∀ φ ∈ schA F κ, l₁ φ = c * l₂ φ := by
  intro F _ _ ψ hψ κ _ L hL hdim l₁ hl₁ l₂ hl₂ hi₁ hi₂ ⟨φ₀, hφ₀, hne⟩
  classical
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := realised_of_mem_closure ψ hψ hg
  have key : ∀ l ∈ (adeleClass F).adm κ, (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
      l (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ) →
      ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    intro l hl hi
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, act_zero_eq_sum]
      exact inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  obtain ⟨c₁, h₁⟩ := key l₁ hl₁ hi₁
  obtain ⟨c₂, h₂⟩ := key l₂ hl₂ hi₂
  obtain ⟨ψ₀, hψ₀, rfl⟩ := hSs φ₀ hφ₀
  have hc₂ : c₂ ≠ 0 := fun h => hne (by rw [h₂ ψ₀ hψ₀, h, zero_mul])
  refine ⟨c₁ / c₂, fun φ hφ => ?_⟩
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  rw [h₁ φ' hφ', h₂ φ' hφ']
  field_simp
end GlobalTheory.AdelicSvN
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


theorem _root_.GlobalTheory.T.linearModel_heisenbergOperators_translation_char : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (K : GL (Fin a') (Fv F Bs.v₁) →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J),
    (∀ g, K g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F Bs.v₁) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = g.val ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (K g)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp σ)) =
        (Γ.V'.J.map Bs.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * Γ.V'.J.map Bs.τ₁) →
    ∀ (S : GL (Fin a') (Fv F Bs.v₁) → ((Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g (γ : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F Bs.v₁) γ →
      ∀ φ ∈ GlobalTheory.WeilM.SB _,
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁)
            (GlobalTheory.LatVac.locCo Γ.M'.co Bs.v₁ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (K g, (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)) γ)) (S g φ)) →
    Continuous (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) ∧ GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ ≠ 1 ∧
    ∃ (wT : Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁))
      (wM : (Matrix (Fin a') (Fin (a + a')) (Fv F Bs.v₁) →ₗ[Fv F Bs.v₁] Fv F Bs.v₁) → (Fin a' × Fin (a + a') → Fv F Bs.v₁) × (Fin a' × Fin (a + a') → Fv F Bs.v₁)),
    ∀ ι, Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι →
      (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ) = fun Y => ι φ (Y + C)) ∧
      (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ) = fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l Y) * ι φ Y) ∧
      (∀ g C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wT C) φ)) =
        fun Y => ι (S g φ) (Y + ((g⁻¹ : GL (Fin a') (Fv F Bs.v₁)).val)ᵀ * C)) ∧
      (∀ g l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁) (wM l) φ)) =
        fun Y => GlobalTheory.LatVac.psiAt Bs.ψ Bs.v₁ (l (g.valᵀ * Y)) * ι (S g φ) Y) := by
  first | exact @GlobalTheory.LinBarOps.heis_ops | exact GlobalTheory.LinBarOps.heis_ops | (intros; apply GlobalTheory.LinBarOps.heis_ops <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

theorem _root_.GlobalTheory.T.restricted_tensor_local_operators : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.InjOn e (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v ψ = 0 → ψ = 0 := by
  first | exact @GlobalTheory.EvKer.ker_trivial | exact GlobalTheory.EvKer.ker_trivial | (intros; apply GlobalTheory.EvKer.ker_trivial <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_vecMulVec_split {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by

  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_inc {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ j, ∑ l, incV F x j * incM F J j l * cA σ (incV F y l) = inclR (F := F) (AF F) (form σ J x y) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl

  simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]

theorem trace_one_tmul (e : E) : Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem eq_zero_of_psi_trace {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AE F E)
    (h : ∀ t : AE F E, ψ (Algebra.trace (AF F) (AE F E) (a * t)) = 1) : a = 0 := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bb : Module.Basis _ (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hco : ∀ i, ∀ x : AE F E, Algebra.trace (AF F) (AE F E) (x * ((1 : AF F) ⊗ₜ[F] b.traceDual i)) = bb.repr x i := by
    intro i x
    conv_lhs => rw [← bb.sum_repr x]

    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, bb, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, trace_one_tmul, mul_comm (b _) (b.traceDual i), Module.Basis.trace_traceDual_mul]
    simp
  refine bb.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have := h (y • ((1 : AF F) ⊗ₜ[F] b.traceDual i))
  rwa [mul_smul_comm, map_smul, hco, smul_eq_mul, mul_comm] at this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vdiff (σ : E →ₐ[F] E) {d : ℕ} (c : Fin d ⊕ Fin d → AE F E) : Fin d → AE F E :=
  fun l => cA σ (c (Sum.inl l)) - cA σ (c (Sum.inr l))

theorem vdiff_add (σ : E →ₐ[F] E) {d : ℕ} (a b : Fin d ⊕ Fin d → AE F E) :
    vdiff σ (a + b) = vdiff σ a + vdiff σ b := by
  funext l
  simp only [vdiff, Pi.add_apply, map_add (f := _)]
  ring

def pairL (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E) :
    (Fin d → AE F E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c)))
  map_add' u u' := by simp only [add_dotProduct, mul_add, map_add (f := _)]
  map_smul' r u := by simp only [smul_dotProduct, mul_smul_comm, map_smul, RingHom.id_apply]

theorem pairL_apply (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E)
    (u : Fin d → AE F E) : pairL σ JW c u = Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c))) := rfl

theorem pairL_add (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (a b : Fin d ⊕ Fin d → AE F E) :
    pairL σ JW (a + b) = pairL σ JW a + pairL σ JW b := by
  refine LinearMap.ext fun u => ?_
  simp only [pairL_apply, LinearMap.add_apply, vdiff_add, Matrix.mulVec_add, dotProduct_add, mul_add, map_add (f := _)]

theorem symp_eq (σ : E →ₐ[F] E) {n n₁ d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (H : Plane E n n₁) (hf : ∑ i, ∑ k, incV F H.y i * incM F JX i k * cA σ (incV F H.x k) = 1)
    (c : Fin d ⊕ Fin d → AE F E) (u : Fin d → AE F E) :
    symp (cA σ) (-1) (incM F JX) (dbl (incM F JW)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c) =
      pairL σ (incM F JW) c u := by
  rw [symp, GlobalTheory.DblSiegelX.zs, hTens_vecMulVec_split, hf, one_mul, pairL_apply]
  congr 2
  have e1 : ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ u) = Sum.elim u u := by
    rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
  have e2 : ∀ U : Fin d ⊕ Fin d → AE F E, ∑ j, ∑ l, U j * dbl (incM F JW) j l * cA σ (c l) =
      U ⬝ᵥ (dbl (incM F JW) *ᵥ fun l => cA σ (c l)) := by
    intro U
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e3 : vdiff σ c = (fun l => cA σ (c (Sum.inl l))) - fun l => cA σ (c (Sum.inr l)) := rfl
  rw [e1, e2, dbl, Matrix.fromBlocks_mulVec, e3, Matrix.mulVec_sub]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.neg_mulVec, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, mul_neg, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rfl

theorem sep (σ : E →ₐ[F] E) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E))
    (hdet : IsUnit JW.det) (u : Fin d → AE F E) (h : ∀ c, ψ (pairL σ JW c u) = 1) : u = 0 := by
  classical
  funext j
  refine eq_zero_of_psi_trace hψ (u j) fun t => ?_
  have := h (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0)
  have hv : vdiff σ (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0) =
      JW⁻¹ *ᵥ Pi.single j (-t) := by
    funext l
    simp [vdiff, GlobalTheory.ArchTraceNondeg.cA_cAinv]
  rw [pairL_apply, hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, dotProduct_single] at this
  simpa [neg_mul, mul_neg] using this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∃ p : (Fin d ⊕ Fin d → AE F E) → (Fin d → AE F E) →ₗ[AF F] AF F, (∀ a b, p (a + b) = p a + p b) ∧
      (∀ c u, p c u = symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c)) ∧
      ∀ u, (∀ c, B.ψ (p c u) = 1) → u = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
  have hcm : IsCMExt F E σ := hP.base.cm
  have hψ : IsStd B.ψ := hP.base.std
  have hf : ∑ i, ∑ k, incV F H.y i * incM F X.J i k * cA σ (incV F H.x k) = 1 := by
    rw [form_inc, form_swap (invol hcm) hP.herm.herm, hH.xy, map_one, map_one]
  have hdet : IsUnit (incM F W.J).det := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := GlobalTheory.ArchTraceNondeg.det_ne_zero_of_hasSig (hP.skew.sig w)
    rw [Matrix.det_smul] at h1
    have h2 : (W.J.map (B.emb w).1).det ≠ 0 := right_ne_zero_of_mul h1
    have h3 : W.J.det ≠ 0 := fun h0 => h2 (by
      have := RingHom.map_det (B.emb w).1 W.J
      rw [h0, map_zero] at this
      exact this.symm)
    have h : (incM F W.J).det = inclR (F := F) (AF F) W.J.det := by rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 h3).map _
  exact ⟨pairL σ (incM F W.J), pairL_add σ _, fun c u => (symp_eq σ X.J W.J H hf c u).symm,
    fun u hu => sep σ hψ _ hdet u hu⟩

end GlobalTheory.DblSiegelChar
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TransvChoose

theorem exists_transversal : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro core F E _ _ _ _ _ σ B n r s X hB hX v w hw g hg
  obtain ⟨O, _, c, ι, P, Q, JL, hloc, hcc, h2, hcx, hinj, hAt, hsupp, hcι, hPQ, hQP, hP, hQ, hJh, hJu, hJ, hlat⟩ :=
    GlobalTheory.T.exists_local_dictionary_inertPlace F E σ B n r s X hB hX v w hw
  haveI := hloc
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := by
    simp [GlobalTheory.DblVac.matD]
  obtain ⟨G, G', hGG, hMG⟩ := GlobalTheory.T.exists_inverse_integral_matrices_preserving_doubled_lattice (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι n P Q (GlobalTheory.InertSph.latAt X v : Set (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) hinj hPQ hQP hP hQ
    (fun z => hlat z) (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv (fun z h1 h2 => by
      obtain ⟨ha, hb⟩ := hg2 z ⟨h1, h2⟩
      exact ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have hgU : (GlobalTheory.DblVac.matD g)ᵀ * Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) * (GlobalTheory.DblVac.matD g).map (cA σ).toRingHom =
      Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) := g.2
  have hU := GlobalTheory.T.unitary_fromBlocks_neg_of_diag_basis_transport (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι (cA σ).toRingHom c n P (incM F X.J) JL hinj hcι hJ (GlobalTheory.DblVac.matD g) G hgU hMG
  obtain ⟨ZL, hZL1, hZL2⟩ := GlobalTheory.T.exists_skewHermitian_correction_isUnit_antidiag_corner O c h2 (fun n J hJ hJd g hgd hgu => core O c hcc h2 hcx n J hJ hJd g hgd hgu)
    n JL G G' hJh hJu hGG hU
  exact GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution F E σ n X v O c ι P Q JL hAt hsupp hcι hPQ hQP hP hQ hJ hlat (GlobalTheory.DblVac.matD g) G ZL hg1 hMG hZL1 hZL2

end GlobalTheory.TransvChoose
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_vacuum_isLocalVacuum_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ∃ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v ∧ s ≠ 0 ∧
      GlobalTheory.Hk3.LocVac ρ s := by
  first | exact @GlobalTheory.InertBridgeVac.vac_locVac | exact GlobalTheory.InertBridgeVac.vac_locVac | (intros; apply GlobalTheory.InertBridgeVac.vac_locVac <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPlace_localHeisenbergOperators_law : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ρ : Matrix (Fin (a + a')) (Fin a') L → Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v)),
      (∀ x (m : SB (Fin a' × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M'.co.rho B.ψ (κ x))
        (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) ((ρ x m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ)) →
    ρ 0 = 1 ∧ ∀ x y, ρ x * ρ y = ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) • ρ (x + y) := by
  first | exact @GlobalTheory.InertRhoLaw.rho_law | exact GlobalTheory.InertRhoLaw.rho_law | (intros; apply GlobalTheory.InertRhoLaw.rho_law <;> assumption)
end
