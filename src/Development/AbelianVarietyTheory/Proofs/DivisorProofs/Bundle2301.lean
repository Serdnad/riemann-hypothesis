module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle117
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle089
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacUniq

theorem dbl_vac_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (φ)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (φ))) → ∃ c : ℂ, φ = c • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hin dd hdd θ _ hvac φ hφ hfix
  classical
  set Λ := latAtV G.V' G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hTr.base.std
  have hnl : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn _
  set vac := G.M'.vac v with hvacdef
  have hvacSB : vac ∈ SB _ := (hTr.geo.hM'.vac v).1
  have hvac0 : vac ≠ 0 := (hTr.geo.hM'.vac v).2.1
  let cf1 : Matrix (Fin a') (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  let cf : Matrix (Fin a') (Fin (a + a') ⊕ Fin (a + a')) (AE F E) → ℂ := fun m =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) m m)
  have hcf : ∀ γ₁ γ₂, cf (Matrix.fromCols γ₁ γ₂) = cf1 γ₁ * star (cf1 γ₂) := by
    intro γ₁ γ₂
    simp only [cf, cf1, GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]

  have hl1 : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) vac = cf1 γ • vac := by
    intro γ hγ
    exact GlobalTheory.TensUniq.eq_of_tens_eq v vac _ _ hvacSB fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v γ (hat γ hγ) vac r hr).symm.trans (hvac γ hγ r hr)

  have hlφ : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φ =
      cf (Matrix.fromCols γ₁ γ₂) • φ := by
    intro γ₁ h₁ γ₂ h₂
    exact GlobalTheory.TensUniq.eq_of_tens_eq v φ _ _ hφ fun r hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ (GlobalTheory.DblVacLine.at_fromCols v (hat _ h₁) (hat _ h₂)) φ r hr).symm.trans
        (hfix γ₁ h₁ γ₂ h₂ r hr)
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).1 (GlobalTheory.LatVac.locCo G.M'.co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v γ₁).2 (-(GlobalTheory.LatVac.locCo G.M'.co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  set φd := boxFun vac (fun x => star (vac x)) with hφd

  have hld : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) φd =
      cf (Matrix.fromCols γ₁ γ₂) • φd := by
    intro γ₁ h₁ γ₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box (GlobalTheory.LatVac.psiAt B.ψ v) hnl, hl1 γ₁ h₁, hl1 γ₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hvac0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show vac t * star (vac t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)

  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V' G.W _ _ _ _ hTr.base hTr.geo.hV' hTr.geo.hW v
  have hunr := (hTr.base.inert v w hin).2.2
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V' G.W v G.M'.co hTr.geo.hV'.lat.toIsLattice hTr.geo.hW.lat.toIsLattice
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M'.co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M'.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hlφ _ i.1.2 _ i.2.2) (fun i => hld _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.DblVacUniq

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.VDblLine

theorem vdbl_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → ∃ c : ℂ, φ = c • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv d' hd' dd hdc θ hθ hvac φ hφSB hφ
  classical
  have hψ := hT.base.std
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  have hnv : ∀ t, ‖GlobalTheory.LatVac.psiAt B.ψ v t‖ = 1 := fun t => hn (GlobalTheory.LatVac.liftV v t)
  set Λ := latAtV G.V G.W v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hatT : ∀ γ ∈ Λ, At (evFin F v) γᵀ := fun γ h u hu => by
    rw [← Matrix.transpose_smul, hat γ h u hu, Matrix.transpose_zero]
  obtain ⟨hvSB, hv0, -⟩ := hT.geo.hM.vac v
  set φ₀ := G.M.vac v with hφ₀
  set φd := boxFun φ₀ (fun x => star (φ₀ x)) with hφd

  have loc : ∀ {κ : Type} [Fintype κ] {W' : Type} [AddCommGroup W'] [Module (AF F) W'] {Bf : W' → W' → AF F}
      (d : Darboux Bf κ) (f : (κ → Fv F v) → ℂ), f ∈ SB _ → ∀ γ, At (evFin F v) γ → ∀ c : ℂ,
      Acts (evFin F v) (d.rho B.ψ γ) f (c • f) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo d v γ) f = c • f := by
    intro κ _ W' _ _ Bf d f hf γ hγ c h
    obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v f hf
    refine GlobalTheory.DblVacLine.eq_of_tens v hr.1 hx₀ ?_
    rw [← GlobalTheory.VacBridge.rho_acts_locCo d B.ψ v γ hγ f r hr]
    exact h r hr
  have hco : ∀ w₁ w₂ : Matrix (Fin a) (Fin (a + a')) (AE F E),
      GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).1 (GlobalTheory.LatVac.locCo G.M.co v w₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M.co v w₁).2 (-(GlobalTheory.LatVac.locCo G.M.co v w₂).2)) := by
    intro w₁ w₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols w₁ᵀ w₂ᵀ)).2 k)) = _
    rw [hdc, hd', hd']
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _
  let χ : Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun γ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ)
  let cf : Matrix (Fin a) (Fin (a + a')) (AE F E) → Matrix (Fin a) (Fin (a + a')) (AE F E) → ℂ := fun w₁ w₂ =>
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ))
  have ht : ∀ w : Matrix (Fin a) (Fin (a + a')) (AE F E),
      symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) wᵀ wᵀ =
        symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w w := fun w => by
    rw [GlobalTheory.WeilTr.symp_transpose (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) _ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) wᵀ wᵀ, Matrix.transpose_transpose]
  have hcf : ∀ w₁ w₂, cf w₁ w₂ = χ w₁ * star (χ w₂) := by
    intro w₁ w₂
    simp only [cf, χ]
    rw [GlobalTheory.DblVacLine.symp_dbl, GlobalTheory.DblVacLine.star_eq_neg B.ψ hn, ht, ht, ← AddChar.map_add_eq_mul, mul_sub,
      sub_eq_add_neg]
  have hvl : ∀ γ ∈ Λ, schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ) φ₀ = χ γ • φ₀ :=
    fun γ h => loc G.M.co φ₀ hvSB γ (hat γ h) _ (hvac γ h)
  have hφl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ = cf w₁ w₂ • φ :=
    fun w₁ h₁ w₂ h₂ => loc dd φ hφSB _ (GlobalTheory.DblVacLine.at_fromCols v (hatT w₁ h₁) (hatT w₂ h₂)) _ (hφ w₁ h₁ w₂ h₂)
  have hdl : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ,
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ᵀ w₂ᵀ)) φd = cf w₁ w₂ • φd := by
    intro w₁ h₁ w₂ h₂
    rw [hco, hφd, GlobalTheory.DblVacLine.schr_box _ hnv, hvl w₁ h₁, hvl w₂ h₂, hcf]
    funext x
    simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul']
    ring

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded G.V G.W v G.M.co hT.geo.hV.lat.toIsLattice hT.geo.hW.lat.toIsLattice
  have hsd := GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B _ _ G.V G.W _ _ _ _ hT.base hT.geo.hV hT.geo.hW v
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt B.ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo G.M.co v)) c hc0 (fun x => (hT.base.inert v w hw).2.2 x)
    (GlobalTheory.LatVac.DualLoc.map_selfDual v G.M.co B.ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hv0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ₀ t * star (φ₀ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt B.ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1ᵀ i.2.1ᵀ))
    (fun i => cf i.1.1 i.2.1) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ φd
    (fun i => hφl _ i.1.2 _ i.2.2) (fun i => hdl _ i.1.2 _ i.2.2) hφd0
  exact ⟨c', hc'⟩

end GlobalTheory.VDblLine

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LocalWeilHom

theorem tens_cancel {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    {R : (κ → AF F) → ℂ} (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x) (hR0 : R 0 ≠ 0)
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z :=
    fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v (y i) u hu
  have hrx : R (0 + z) = R 0 := hR 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ]
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₂ : ∀ Φ ∈ schA F κ, T₂ Φ ∈ schA F κ)
    {φ φ' φ'' : (κ → Fv F v) → ℂ} (h₂ : Acts (evFin F v) T₂ φ φ') (h₁ : Acts (evFin F v) T₁ φ' φ'') :
    Acts (evFin F v) (T₁ * T₂) φ φ'' := by
  intro r hr
  have e₂ := h₂ r hr
  have hr' : Rest (evFin F v) φ' r := ⟨hr.1, by rw [← e₂]; exact hT₂ _ hr.2⟩
  show T₁ (T₂ (tens (evFin F v) φ r)) = _
  rw [e₂]
  exact h₁ r hr'

theorem exists_hom {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {κ : Type} [Fintype κ] {Γ : Type} [Monoid Γ]
    (ρ : Γ →* Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ γ, ∀ Φ ∈ schA F κ, ρ γ Φ ∈ schA F κ)
    (hex : ∀ γ, ∀ m ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (ρ γ) m φ₁) :
    ∃ ω : Γ →* Module.End ℂ (SB (κ → Fv F v)), ∀ γ (m : SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      φ₁ ∈ SB (κ → Fv F v) → (Acts (evFin F v) (ρ γ) (m : (κ → Fv F v) → ℂ) φ₁ ↔ ((ω γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = φ₁) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (SB _).zero_mem).1
  choose f hfSB hfA using hex

  have hread : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (ρ γ) m φ₁ → ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R :=
    fun γ m hm φ₁ h => h R (hR m hm)
  have huniq : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R → f γ m hm = φ₁ := by
    intro γ m hm φ₁ h
    exact tens_cancel v hRi hR0 ((hread γ m hm _ (hfA γ m hm)).symm.trans h)
  have htadd : ∀ φ φ' : (κ → Fv F v) → ℂ, tens (evFin F v) (φ + φ') R =
      tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro φ φ'; funext x; simp only [tens, Pi.add_apply, add_mul]
  have htsmul : ∀ (c : ℂ) (φ : (κ → Fv F v) → ℂ), tens (evFin F v) (c • φ) R = c • tens (evFin F v) φ R := by
    intro c φ; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Γ → Module.End ℂ (SB (κ → Fv F v)) := fun γ =>
    { toFun := fun m => ⟨f γ m m.2, hfSB γ m m.2⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        show f γ _ _ = f γ m m.2 + f γ m' m'.2
        apply huniq
        rw [Submodule.coe_add, htadd, map_add (f := _), hread γ m m.2 _ (hfA γ m m.2),
          hread γ m' m'.2 _ (hfA γ m' m'.2), htadd]
      map_smul' := fun c m => by
        apply Subtype.ext
        show f γ _ _ = c • f γ m m.2
        apply huniq
        rw [Submodule.coe_smul, htsmul, map_smul, hread γ m m.2 _ (hfA γ m m.2), htsmul] }
  have hL : ∀ γ (m : SB (κ → Fv F v)), ((L γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = f γ m m.2 := fun _ _ => rfl
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    apply huniq
    rw [map_one]; rfl
  · intro γ γ'
    apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    show f (γ * γ') m m.2 = f γ (f γ' m m.2) (hfSB γ' m m.2)
    apply huniq
    rw [map_mul]
    exact acts_mul v (ρ γ) (ρ γ') (hpres γ') (hfA γ' m m.2) (hfA γ _ (hfSB γ' m m.2)) R (hR m m.2)
  · intro γ m φ₁ _
    show _ ↔ f γ m m.2 = φ₁
    constructor
    · intro h; exact huniq γ m m.2 φ₁ (hread γ m m.2 φ₁ h)
    · intro h; rw [← h]; exact hfA γ m m.2

end GlobalTheory.LocalWeilHom

namespace GlobalTheory.LocalWeilHom

theorem local_weil_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ σL JS JT ιS ιT hιS hιT
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  let ρ := om'.comp (MonoidHom.prodMap ιS ιT)
  have hρ : ∀ g h, ρ (g, h) = om' (ιS g, ιT h) := fun _ _ => rfl
  have hpres : ∀ γ, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ρ γ Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun γ Φ hΦ => hW.pres _ Φ hΦ
  have hex : ∀ γ, ∀ m ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (ρ γ) m φ₁ := by
    rintro ⟨g, h⟩ m hm
    obtain ⟨φ₁, hφ₁, hA₁⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v (ιT h) (hιT h) m hm
    obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hTr v (ιS g) (hιS g)
    refine ⟨S φ₁, (hS φ₁ hφ₁).1, ?_⟩
    have hsplit : ρ (g, h) = om' (ιS g, 1) * om' (1, ιT h) := by
      rw [hρ, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact acts_mul v _ _ (fun Φ hΦ => hW.pres _ Φ hΦ) hA₁ (hS φ₁ hφ₁).2
  obtain ⟨ω, hω⟩ := exists_hom v ρ hpres hex
  exact ⟨ω, fun g h m φ₁ hφ₁ => hω (g, h) m φ₁ hφ₁⟩

end GlobalTheory.LocalWeilHom

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ThetaNormal

theorem thetaNZ_of_polAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) → GlobalTheory.LN.SplitOver t.G (IsLocalRing.maximalIdeal R) → GlobalTheory.LN.ThetaNZ t.G t.PP.L := by
  intro E _ _ _ H R _ _ _ hA t hpol hs
  obtain ⟨h1, h2, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨A, -, gen, hgen, hL, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt h1 h2 E H R t hpol
  have := hA.1.1
  obtain ⟨P, hPL, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric h1 R A t.G t.semi gen hgen t.PP t.cub t.sym
  have hσ : ∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0 := by
    rw [hPL]; exact GlobalTheory.T.exists_nonzero_section_of_polarised_generic_fibre E H R t hpol
  obtain ⟨D, U, hUL, -⟩ := GlobalTheory.T.semiabelian_generic_fibre_polarization_iso R hA t.G P t.semi (hPL ▸ GlobalTheory.LN.UnifPrime.hypW_of_triple t) hs A gen hgen
    (hPL ▸ hL) hσ
  have key := GlobalTheory.T.exists_section_nonzero_on_closed_fibre_complete_local R hA.1.1 hA.1.2.2.1 hA.2.1 hA.2.2.1 D A t.G t.semi U
  rw [hUL, hPL] at key
  have := t.semi.smooth
  exact GlobalTheory.UnifNormal.thetaNZ_of_closedPoint t.G _ key

end GlobalTheory.ThetaNormal
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem form_eq_zero_of_evForm_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens) (ξ : Ω[Sec (str A) U.1⁄ℂ]), (∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ = 0) → ξ = 0 := by
  intro A _ g L u hA U ξ hξ
  obtain ⟨d, ω, -, -, -, hsum, hev⟩ := GlobalTheory.T.kaehler_differentials_free_coordinate_forms_abelian A g L u hA U
  have hz : ∀ a, (d a).liftKaehlerDifferential ξ = 0 := by
    intro a
    apply GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA U.1
    intro z hz
    rw [← hev a ξ z hz, hξ z hz]
    rfl
  rw [hsum ξ]
  simp [hz]

end GlobalTheory
end
