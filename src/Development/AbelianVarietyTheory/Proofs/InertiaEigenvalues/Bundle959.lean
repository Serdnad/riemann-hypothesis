module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle902
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle955
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle285
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle269
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2532
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle022
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle920
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle789
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem span_preimage_eq_top {L V W ι : Type*} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    (e : L →+* ℂ) (f : V →ₛₗ[e] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun i => f (b i))) (hsp : Submodule.span ℂ (Set.range (fun i => f (b i))) = ⊤)
    (S : Set W) (hS : Submodule.span ℂ S = ⊤) (hsub : ∀ y ∈ S, y ∈ Set.range f) :
    Submodule.span L {x | f x ∈ S} = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  let B : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let Φ : W →ₗ[ℂ] ℂ := B.constr ℂ (fun i => e (φ (b i)))
  have key : ∀ x, Φ (f x) = e (φ x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.mem_span x
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have : f (b i) = B i := (Module.Basis.mk_apply hli hsp.ge i).symm
      rw [this]
      exact B.constr_basis ℂ _ i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hΦ : Φ = 0 := by
    refine LinearMap.ext_on hS fun y hy => ?_
    obtain ⟨x, rfl⟩ := hsub y hy
    have : φ x = 0 := hφ (Submodule.subset_span hy)
    rw [key, this, map_zero, LinearMap.zero_apply]
  apply hφ0
  ext x
  have := key x
  rw [hΦ, LinearMap.zero_apply] at this
  exact e.injective (by rw [← this, LinearMap.zero_apply, map_zero])

theorem span_latS : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  intro D w j
  have h := D.what₂.jMt_basis (D.what₂.muTw w) j (Module.Free.chooseBasis _ _)
  exact span_preimage_eq_top D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) _ h.1 h.2 _
    (D.what₂.MtLat (D.what₂.muTw w) j).span_top (fun y hy => D.what₂.MtLat_sub _ _ y hy)

end GlobalTheory.PlaceRead
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefRowMod

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace



theorem main : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G]
    (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0),
    GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt →
    ∀ (i : Fin D.R.m), ∃ X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1), GlobalTheory.RefTheta.IsCanonR Y i rfl X := by
  intro hH hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP _ hEx j
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hmod := hcore.models
  have hθ := hmod.inf
  have hν := hmod.νW j
  have hHaar : (R.νW j).IsHaarMeasure := hν.1.1
  have hFD := hν.2
  have hSig : (Wc D j).SigOK := D.sp.W_sig _
  have hSA : SchurAll D := fun V _ S θ M J χ μ 𝓕 => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ μ 𝓕).2
  have hHA : HCAll D := fun V _ S θ M J χ => (GlobalTheory.MultFinite.hcFinite_and_schurMult hH hC D θ V S M J χ 0 ∅).1
  have hStd : GlobalTheory.Mem.R3.StdFrame Y.hF (Y.PW j) := Y.stdPsi.2 j
  have hcc := GlobalTheory.T.unitary_congruence_conj_contains_congruence D.host.E D.R.r
  obtain ⟨hlin, hherm, hpos⟩ := GlobalTheory.FinTypesRows.minf_sesq (M := R.MW j (sg0 D A3.A)) (θ := R.θ) (R.νW j) (R.fdW j)
    (Y.PW j) hSA hSig hθ hHaar hFD
  have hT := Y.tied.lift
  have hLev := GlobalTheory.FinTypesRows.levOK_levS (Y.PW j) hStd (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))
  set c : ℝ := (∏ ρ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) ρ) : ℚ) : ℝ)) * (RealDat.nP F.lv2 false)⁻¹ with hcdef
  have hc : 0 < c := mul_pos (Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.EasyInputs.dimOK D j (sg0 D A3.A) ρ)
    (inv_pos.2 (RealDat.nP_pos false))
  have hSm := GlobalTheory.Mem.EasyInputs.smAll D (Wc D j) _ (R.MW j (sg0 D A3.A))
  have hex : ∀ x ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)), ∀ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)),
      ∃ b, Mult.IsMultIP (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y b := by
    intro x hx y hy
    obtain ⟨N, -, hx', hy'⟩ := GlobalTheory.FinTypesRows.exists_common (Y.PW j) hx hy
    exact hSA _ hSig _ R.θ _ _ _ _ _ hθ hHaar hFD x hx' y hy'
  let φ : D.what₂.Mj (j.1 + 1) →ₗ[ℂ] Mult.MMap (R.MW j (sg0 D A3.A)) :=
    (PiTensorProduct.lift : Mult.MMap (R.MW j (sg0 D A3.A)) ≃ₗ[ℂ] _).symm.toLinearMap ∘ₗ
      (Submodule.subtype ((toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj).Wc j)) ∘ₗ (Y.IL.jMj j).toLinearMap
  have hφ : ∀ y, PiTensorProduct.lift (φ y) = (Y.IL.jMj j y).1 := by
    intro y
    exact LinearEquiv.apply_symm_apply _ _
  have hgood : ∀ y, φ y ∈ Mult.goodPart R.θ (R.MW j (sg0 D A3.A)) (levS _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW j) (R.datWp j (R.levL F.lv2 false (sg0 D A3.A)))) (R.eWf j (sg0 D A3.A)) := by
    intro y
    obtain ⟨a, ha, hay⟩ := (Y.IL.jMj j y).2
    have : φ y = a := by
      show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
      rw [← hay]
      exact LinearEquiv.symm_apply_apply _ _
    rw [this]
    exact ha
  have hmem : ∀ y, φ y ∈ principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A)) := fun y =>
    principalLevelFrame.mult_le_Minf hLev (Mult.goodPart_le _ _ _ _ _ (hgood y))
  refine ⟨{ A := Mult.MMap (R.MW j (sg0 D A3.A))
            ρ := principalLevelFrame.actM (Y.PW j) (R.MW j (sg0 D A3.A))
            C := principalLevelFrame.Minf R.θ (Y.PW j) (R.MW j (sg0 D A3.A))
            B := fun x y => (c : ℂ) * Mult.ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) x y
            lin := fun x hx y hy z hz c' => by
              rw [hlin x hx y hy z hz c']
              ring
            herm := fun x hx y hy => by
              rw [map_mul, Complex.conj_ofReal, ← hherm x hx y hy]
            pos := fun x hx hx0 => by
              rw [Complex.re_ofReal_mul]
              exact mul_pos hc (hpos x hx hx0)
            stab := fun h x hx => GlobalTheory.FinTypesRows.minf_stable (Y.PW j) hcc h hx
            inv := fun h x hx y hy => by
              rw [GlobalTheory.T.schur_pairing_invariant_under_standard_group D (Wc D j) _ R.θ (R.MW j (sg0 D A3.A)) D.R.r (Y.PW j) (R.νW j) (R.fdW j) hSA hSig hθ
                hHaar hFD h x hx y hy]
            smooth := fun x hx => GlobalTheory.FinTypesRows.minf_smooth (Y.PW j) hx
            adm := fun N hN => GlobalTheory.FinTypesRows.minf_adm (Y.PW j) hHA hSig hθ (GlobalTheory.FinTypesRows.levN_open (Y.PW j) hStd) N hN
            φ := φ
            φ_mem := hmem
            φ_inner := fun x y => by
              beta_reduce
              rw [hT.mj j x y]
              change (∏ τ, ((Mult.dimK _ _ (kapAt (Wc D j) (sg0 D A3.A) τ) : ℚ) : ℂ)) *
                Mult.ipM (R.MW j (sg0 D A3.A)) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.νW j) (R.fdW j) (φ x) (φ y) = _
              rw [GlobalTheory.RowModCanon.ipM_smul_measure _ hSm _ _ (inv_nonneg.2 (RealDat.nP_pos false).le) _ _
                (hex _ (hmem x) _ (hmem y)), hcdef]
              push_cast
              ring
            isot := fun σ y => by
              rw [hT.isot j σ y, Y.prtWE j σ]
              constructor
              · rintro ⟨a, ha, hay⟩
                have e : φ y = a := by
                  show PiTensorProduct.lift.symm (Y.IL.jMj j y).1 = a
                  rw [← hay]
                  exact LinearEquiv.symm_apply_apply _ _
                rw [e]
                exact (Submodule.mem_inf.1 ha).2
              · intro h
                exact ⟨φ y, Submodule.mem_inf.2 ⟨hgood y, h⟩, hφ y⟩ }, LinearMap.id, c, Function.injective_id, hc,
    Submodule.map_id _, fun h x => rfl, fun x _ y _ => rfl, fun y => hφ y⟩

end GlobalTheory.RefRowMod
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

noncomputable section

namespace GlobalTheory.RefThetaRead

open MeasureTheory Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.principalLevelFrame Formalism.IndefR.Mult
  Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.ThetaTri GlobalTheory.ThetaRead
open scoped TensorProduct InnerProductSpace

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem fire (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) :
    ThetaFireRow (toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj) Y.IL :=
  ⟨fun μ _ i => GlobalTheory.ThetaPRead.isThetaP_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.thP.thF μ i,
    GlobalTheory.ThetaFireLift.thetaFireL R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.lev core.grp core.models
      core.thP R.toRealDat.hv0 Y.IL,
    GlobalTheory.LiftResInj.resInjL_toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj core.models.inf⟩



theorem ipM_theta (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2)
    (hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T' T'' : MMap (R.MW j (sg0 D A3.A))) (hT : PiTensorProduct.lift T' = (Y.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T'' = (Y.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (R.MW j (sg0 D A3.A)) (R.νW j) (R.fdW j) T' T'' =
      ∫ g in R.fdW j, star (PiTensorProduct.lift T' (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g) *
        (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
          (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ)))
        ∂(R.νW j) := by
  have hM := core.models
  have hF := fire Y core
  obtain ⟨w, hw1, hw2, hw3⟩ := hF.2.1 μ hμ j x
  have hth := Y.tied.lift.theta μ hμ j x w (hF.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (Y.IL.jMj j y).2
  have hTT : T₀ = T' := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T'' = postOn (R.MW j (sg0 D A3.A)) (R.eWf j (sg0 D A3.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (R.MW j (sg0 D A3.A)) _ U).symm
  have hin : ∀ g, (∫ h in R.fdV j (Y.tupT μ), thetaKO (R.ωP j (Y.tupT μ)) h g
      (R.ptP j (Y.tupT μ) (R.ioP j (kUnit (R.MW j (sg0 D A3.A))) ((Y.IL.jMt μ hμ j x).1 h))) ∂(R.νV j (Y.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (R.MW j (sg0 D A3.A)))) g := by
    intro g
    have e1 := (hF.1 _ hμ j).eq (Y.IL.jMt μ hμ j x) (kUnit (R.MW j (sg0 D A3.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj R.toRealDat hM hX j (mult_le_wall R.toRealDat F.lv2 false j hT1)
    (mult_le_wall R.toRealDat F.lv2 false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (R.MW j (sg0 D A3.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := hF.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (R.MW j (sg0 D A3.A)) _ _ _ _ hU0 _



theorem fV_eq (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (core : GlobalTheory.Hk3.Core R.toRealDat F.lv2) {M : MtFam D}
    (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1))
    (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ))
    (hFm : (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) =
      (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x) :
    GlobalTheory.RefTheta.fV Ad i Fm = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := by
  have e : (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) =
      fun k => (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ((Ad.PV i).ψ (preF (Ad.PV i) k)) := by
    funext k
    rw [hFm]
    exact Ad.read _ _ i x _
  change (R.cV i).ext (fun k => Ad.eW D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i
      ((Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) (preF (Ad.PV i) k))) = _
  rw [e]
  obtain ⟨z, hz⟩ : (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 ∈
      LinearMap.range (R.extV i (Y.tupT D.what₂.mu0)) := (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).2.1
  have hz' : (R.cV i).ext ((R.HV i (Y.tupT D.what₂.mu0)).e z) = (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 := hz
  generalize (Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (core.models.cV i).1 _ _



theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (x : D.what₂.Mt D.what₂.mu0 (i.1 + 1)) (y : D.what₂.Mj (i.1 + 1)) (Fm : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)), (Fm : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).real x → inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.RefTheta.phi0 Y i) Fm ⟨X.φ y, X.φ_mem y⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hEx M Ad i X hc x y Fm hFm
  have core := (GlobalTheory.CoreOfWeak.core_of_weak R F hP.char hEx).1
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hH.ok.ok2.irr
  have hf := fV_eq Y core Ad i x Fm hFm
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  have key : inner ℂ y (D.what₂.thetaP D.what₂.mu0 (i.1 + 1) x) = (GlobalTheory.RefTheta.cC hc : ℂ) *
      ∫ g in R.fdW i, star (GlobalTheory.RefTheta.yv hc ⟨X.φ y, X.φ_mem y⟩ g) *
        (∫ h in R.fdV i (Y.tupT D.what₂.mu0), thetaKO (R.ωP i (Y.tupT D.what₂.mu0)) h g
          (GlobalTheory.RefTheta.phi0 Y i ((Y.IL.jMt D.what₂.mu0 (GlobalTheory.RefTheta.reference_tuple_used D) i x).1 h))
            ∂(R.νV i (Y.tupT D.what₂.mu0))) ∂(R.νW i) := by
    refine (X.φ_inner _ _).trans ((hB _ (X.φ_mem _) _ (X.φ_mem _)).trans (congrArg (fun z => (GlobalTheory.RefTheta.cC hc : ℂ) * z) ?_))
    exact ipM_theta Y core hX (GlobalTheory.RefTheta.reference_tuple_used D) i x y _ _ (hφ y) (hφ _)
  rw [key, ← hf]
  rfl

end GlobalTheory.RefThetaRead

end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.rationalLatticeTwistedTuple_span_top : ∀ (D : D7) (w : D.what₂.places.Pl) (j : ℕ), Submodule.span D.what₂.LL (latS (D := D) w j) = ⊤ := by
  first | exact @GlobalTheory.PlaceRead.span_latS | exact GlobalTheory.PlaceRead.span_latS | (intros; apply GlobalTheory.PlaceRead.span_latS <;> assumption)

end
end
