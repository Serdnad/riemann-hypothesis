module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CechDeRhamCoefMapOneFormsRestrictAlongFunctor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle766
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle942
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle454
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem liftSemi_pullHyp1_bijective_of_finite : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullHyp1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ _ C _ _ _ F F' α hn hs hb
  let m : CoefMap (algebraMap R R') F F' := ⟨𝟭 C, α, hn, hs⟩
  let g : Tot0 F →ₛₗ[algebraMap R R'] Tot0 F' :=
    { toFun := fun x T ↦ α T (x T)
      map_add' := fun x y ↦ funext fun T ↦ map_add (α T) (x T) (y T)
      map_smul' := fun r x ↦ funext fun T ↦ hs T r (x T) }
  have h0 : Function.Bijective (liftSemi g) :=
    GlobalTheory.T.bijective_liftSemi_tot0_of_bijective R R' C F F' α hn hs hb g fun _ _ ↦ rfl
  have h1 : Function.Bijective (liftSemi (pullTot1 m)) := GlobalTheory.T.totalOneCochains_baseChange_bijective_finiteCategory R R' C F F' α hn hs hb
  have h2 : Function.Bijective (liftSemi (pullTot2 m)) := GlobalTheory.T.totalTwoCochains_finiteCategory_baseChange_bijective R R' C F F' α hn hs hb
  have hZ : Function.Bijective (liftSemi (pullZZ1 m)) :=
    GlobalTheory.KerFlat.main R R' (cechDeRhamTotalCocyclesOne F) (Tot1 F) (Tot2 F) (cechDeRhamTotalCocyclesOne F') (Tot1 F') (Tot2 F')
      (cechDeRhamTotalCocyclesOne F).subtype (dTot1 F) (cechDeRhamTotalCocyclesOne F').subtype (dTot1 F') (pullZZ1 m) (pullTot1 m) (pullTot2 m)
      (cechDeRhamTotalCocyclesOne F).injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F))
      (cechDeRhamTotalCocyclesOne F').injective_subtype (LinearMap.exact_subtype_ker_map (dTot1 F'))
      (fun _ ↦ rfl) (fun x ↦ (pullTot2_dTot1 m x).symm) h1 h2.1
  exact GlobalTheory.liftSemi_bijective_of_exact_cokernel R R' (Tot0 F) (cechDeRhamTotalCocyclesOne F) (Hyp1 F) (Tot0 F') (cechDeRhamTotalCocyclesOne F') (Hyp1 F')
    ((dTot0 F).codRestrict (cechDeRhamTotalCocyclesOne F) (dTot0_mem F)) (Hyp1.mk F)
    ((dTot0 F').codRestrict (cechDeRhamTotalCocyclesOne F') (dTot0_mem F')) (Hyp1.mk F') g (pullZZ1 m) (pullHyp1 m)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F)
    (LinearMap.exact_map_mkQ_range _) (Hyp1.mk_surjective F')
    (fun x ↦ Subtype.ext (pullTot1_dTot0 m x).symm) (fun z ↦ (pullHyp1_mk m z).symm) h0.2 hZ

end GlobalTheory
end

section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.PDivGroup.DimSum

theorem baseChange_bijective_of_ker {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : Type) [CommRing k] [Algebra O k] (a : O)
    (ha : algebraMap O k a = 0) (f : M →ₗ[O] N) (hf : Function.Surjective f)
    (hfa : ∀ v, f (a • v) = 0) (hk : ∀ w, f w = 0 → ∃ v, w = a • v) :
    Function.Bijective (f.baseChange k) := by
  rw [LinearMap.baseChange_eq_ltensor]
  refine ⟨?_, LinearMap.lTensor_surjective k hf⟩
  have hex : Function.Exact (a • LinearMap.id : M →ₗ[O] M) f := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, rfl⟩ := hk w hw
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact hfa v
  have hex' := lTensor_exact k hex hf
  have hz : LinearMap.lTensor k (a • LinearMap.id : M →ₗ[O] M) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ha, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex' x).1 hx
  rw [hz, LinearMap.zero_apply]

open GlobalTheory.PDiv Module

theorem finrank_cot_baseChange_one {p : ℕ} {O : Type} [CommRing O] (H : PDivGroup p O) (k : Type)
    [Field k] [Algebra O k] (hp : algebraMap O k p = 0) :
    finrank k (Cot k (k ⊗[O] H.A 1)) = finrank k (k ⊗[O] H.omega) := by
  have h1 : Function.Bijective ((H.omegaLevel 1).baseChange k) :=
    baseChange_bijective_of_ker k (p : O) hp (H.omegaLevel 1) (H.omegaLevel_surjective 1)
      (fun v => by
        have := H.pow_smul_cot 1 (v.1 1)
        rw [pow_one] at this
        exact this)
      (fun w hw => by
        obtain ⟨v, hv⟩ := (H.omega_val_eq_zero_iff 1 w).1 hw
        exact ⟨v, by rw [hv, pow_one]⟩)
  let e1 := LinearEquiv.ofBijective _ h1
  let e2 := LinearEquiv.ofBijective _ (liftSemi_toBaseChange_cot_bijective O k (H.A 1))
  exact (e1.trans e2).finrank_eq.symm

theorem finrank_cot_congr {k X Y : Type} [Field k] [CommRing X] [CommRing Y] [Bialgebra k X]
    [Bialgebra k Y] (e : X ≃ₐc[k] Y) : finrank k (Cot k X) = finrank k (Cot k Y) := by
  have h1 : (e.symm : Y →ₐc[k] X).comp (e : X →ₐc[k] Y) = BialgHom.id k X :=
    BialgHom.ext fun x => e.symm_apply_apply x
  have h2 : (e : X →ₐc[k] Y).comp (e.symm : Y →ₐc[k] X) = BialgHom.id k Y :=
    BialgHom.ext fun x => e.apply_symm_apply x
  refine (LinearEquiv.ofLinear (cotMap (e : X →ₐc[k] Y)) (cotMap (e.symm : Y →ₐc[k] X)) ?_ ?_).finrank_eq
  · rw [← cotMap_comp, h2, cotMap_id]
  · rw [← cotMap_comp, h1, cotMap_id]

end GlobalTheory.PDivGroup.DimSum


open Module PDiv in
theorem GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
      d + Module.finrank O G.dual.Lie = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let k := IsLocalRing.ResidueField O
  have hpk : algebraMap O k p = 0 := by
    change IsLocalRing.residue O p = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : O))
  have hpk' : ((p : ℕ) : k) = 0 := by rw [← map_natCast (algebraMap O k), hpk]
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let eG : (Fin d → O) ≃ₗ[O] G.omega := LinearEquiv.ofBijective _ hbij
  haveI : Module.Free O G.omega := Module.Free.of_equiv eG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  have hd : finrank O G.omega = d := by rw [← eG.finrank_eq, Module.finrank_fin_fun]
  have hLie : finrank O G.dual.Lie = finrank O G.dual.omega := by
    let b := Module.Free.chooseBasis O G.dual.omega
    rw [finrank_eq_card_basis b.dualBasis, finrank_eq_card_basis b]
  obtain ⟨-, -, -, hsum⟩ := finrank_rigExt_omega p k hpk' (G.baseChange k)
  have hA : finrank k (G.baseChange k).omega = finrank O G.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).omegaLevel_one_bijective hpk')).finrank_eq]
    exact (DimSum.finrank_cot_baseChange_one G k hpk).trans (Module.finrank_baseChange)
  have hB : finrank k (G.baseChange k).dual.omega = finrank O G.dual.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).dual.omegaLevel_one_bijective hpk')).finrank_eq]
    refine (DimSum.finrank_cot_congr (CartierDual.baseChange O k (G.A 1))).symm.trans ?_
    exact (DimSum.finrank_cot_baseChange_one G.dual k hpk).trans (Module.finrank_baseChange)
  rw [hLie, ← hd, ← hA, ← hB]
  exact hsum
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.lift_quasiLogarithm_along_pdThickening : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (g : MvPowerSeries (Fin d) C) (w : Fin d → B), QL (fun i => map θ (μ i)) ⊤ g → (∀ i, lin g i = algebraMap O C (θ (w i))) → ∃ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f ∧ map Θ f = g ∧ ∀ i, lin f i = algebraMap B Q (w i) := by
  first | exact @GlobalTheory.QLog.KLift.lift_quasiLog | exact GlobalTheory.QLog.KLift.lift_quasiLog | (intros; apply GlobalTheory.QLog.KLift.lift_quasiLog <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.Chart

theorem exists_series_of_cobOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 →
    ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k),
      IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  intro p _ k _ d G c μ hμ b hb
  obtain ⟨x, cc, B, -, hcob, hcounit, hB1⟩ := PDivGroup.exists_of_cobOne_eq_zero (G := G) hb
  have hfun := Chart.functions_are_series p k d G c
  have hsq := chart_square_presents p k d G c
  obtain ⟨Bs, hBs, -⟩ := hfun.2.2 B.1 B.2
  obtain ⟨κ, hκ, -⟩ := hsq.2 cc.1 (fun n => (cc.2 n).2)
  have hlaw := (LawCoord.main p k d G c).2 μ hμ
  have hcoc : IsCoc μ κ := (isCoc_iff_mem_cocycles p k d G c μ hμ κ).2 (by
    have e : (fun n => c.ev₂ n κ) = cc.1 := funext hκ
    rw [e]; exact cc.2)
  have hmap := (isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw p k d G c μ hμ p)
  have hid : cob1 μ Bs = pull2 (nmul μ p) κ := by
    obtain ⟨s, -, hs⟩ := hsq.2 (fun n => c.ev₂ n (cob1 μ Bs)) (fun n => hfun.2.1 n _)
    refine (hs _ fun n => rfl).trans (hs _ fun n => ?_).symm
    rw [(hmap.2 n).2, hκ, (hlaw.2 n Bs).2, hBs]
    exact (congrArg (fun z : G.cocycles => z.1 n) hcob).symm
  have hB0 : constantCoeff Bs = 0 := by
    have h := (counit_dUnit_evA k d (G.A 1) (c.x 1) (c.nil 1) (c.aug 1) Bs).1
    rw [← h]
    change Coalgebra.counit (R := k) (c.ev 1 Bs) = 0
    rw [hBs 1, hB1, hcounit]
  have hX : ∀ (σ : Type) (i : σ), constantCoeff (X i : MvPowerSeries σ k) = 0 :=
    fun _ i => constantCoeff_X i
  have hL : ∀ j, constantCoeff (inL (nmul μ p j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hR : ∀ j, constantCoeff (inR (nmul μ p j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hκ0 : constantCoeff κ = 0 := by
    have h1 := (SubstCalc.powerSeriesEvalTwoGroups_rules_alt k d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) _ _ hL hR).2.2.2.1 κ
    have h2 : constantCoeff (cob1 μ Bs) = 0 := by
      unfold cob1 inL inR
      rw [map_sub, map_sub, SubstCalc.constantCoeff_subst_of_zero hlaw.1,
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _),
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hB0, sub_zero, sub_zero]
    rw [← h1, ← h2, hid]
    rfl
  exact ⟨κ, Bs, hcoc, hκ0, hid, (hBs 1).trans hB1⟩

end GlobalTheory.Katz.Chart
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  first | exact @GlobalTheory.Katz.isCoc_iff_mem_cocycles | exact GlobalTheory.Katz.isCoc_iff_mem_cocycles | (intros; apply GlobalTheory.Katz.isCoc_iff_mem_cocycles <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_galoisConj_eigenSystem_congruent : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  first | exact @GlobalTheory.ExpFrame.Conj.exists_eig_congr | exact GlobalTheory.ExpFrame.Conj.exists_eig_congr | (intros; apply GlobalTheory.ExpFrame.Conj.exists_eig_congr <;> assumption)
end

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbertTwistedLattice_jets_modular_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (α : ι → Matrix (Fin 2) (Fin 2) (ZMod N)) (Ch : ι → ℍ → ℂ) (κ : Emb F → ℕ), (∀ i γ, α (act i γ) = α i * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) → (∀ i (γ : SL(2, ℤ)) (τ : ℍ), Ch i (γ • τ) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) ^ 2 * Ch (act i γ) τ - ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (τ : ℂ) + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) / (2 * Real.pi * Complex.I)) → IsFam act (wt (2 * s) κ : ℕ) (fun i ↦ hfun (2 * s) (twist N L (α i)) κ (Ch i)) := by
  first | exact @GlobalTheory.HilbFam.isFam_hfun_twist | exact GlobalTheory.HilbFam.isFam_hfun_twist | (intros; apply GlobalTheory.HilbFam.isFam_hfun_twist <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply stalkLinear)

namespace GlobalTheory.VB.Ker

section Algebra

variable {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

theorem bijective_sumElim_iff {ι κ : Type} [Fintype ι] [Fintype κ] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (e : ι → M₁) (t : κ → M₂)
    (ht : Function.Bijective (Fintype.linearCombination R fun j => g (t j))) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t)) ↔
      Function.Bijective (Fintype.linearCombination R e) := by
  have h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a =
      f (Fintype.linearCombination R e fun i => a (.inl i)) +
        Fintype.linearCombination R t fun j => a (.inr j) := by

    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]
  have h2 (b : κ → R) : g (Fintype.linearCombination R t b) =
      Fintype.linearCombination R (fun j => g (t j)) b := by

    simp [Fintype.linearCombination_apply, map_sum]
  have h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0 := by
    have := congrArg g h
    rw [map_add (f := _), hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2] at this
    exact ht.1 (this.trans (map_zero _).symm)
  constructor
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · have : Sum.elim a (0 : κ → R) = 0 := H.1 (by
        rw [h1, map_zero]
        change f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0
        rw [ha, map_zero, map_zero, add_zero])
      exact funext fun i => congrFun this (.inl i)
    · obtain ⟨a, ha⟩ := H.2 (f m)
      rw [h1] at ha
      rw [h3 _ _ _ ha, map_zero, add_zero] at ha
      exact ⟨_, hf ha⟩
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · rw [h1, ← map_zero f] at ha
      have hb := h3 _ _ _ ha
      rw [hb, map_zero, add_zero] at ha
      have ha' := H.1 ((hf ha).trans (map_zero _).symm)
      funext k
      rcases k with i | j
      exacts [congrFun ha' i, congrFun hb j]
    · obtain ⟨b, hb⟩ := ht.2 (g m)
      obtain ⟨n, hn⟩ := (hfg (m - Fintype.linearCombination R t b)).1 (by
        rw [map_sub, h2, hb, sub_self])
      obtain ⟨a, rfl⟩ := H.2 n
      exact ⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩

theorem nonempty_basis_of_exact [IsLocalRing R] {r s : ℕ} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis (Fin (r + s)) R M₂)
    (c : Module.Basis (Fin s) R M₃) : Nonempty (Module.Basis (Fin r) R M₁) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis c
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨φ, hφ, -⟩ := hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩
  let π : M₂ →ₗ[R] M₁ := LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap
  have hπ : π ∘ₗ f = LinearMap.id := by
    ext m
    simp [π, hφ]
  have : Module.Projective R M₁ := .of_split f π hπ
  have : Module.Finite R M₁ := .of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩
  have : Module.Free R M₁ := Module.free_of_flat_of_isLocalRing
  have h := φ.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
    Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩

theorem bijective_iff_isUnit_det {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M₁)
    (v : ι → M₁) : Function.Bijective (Fintype.linearCombination R v) ↔ IsUnit (b.det v) := by
  rw [← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.range_eq_top, Fintype.range_linearCombination]

end Algebra

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem exists_germ_eq_family {x : X} (hx : x ∈ U) (a : ι → (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (e : ι → Γ(F, V)),
      ∀ i, F.presheaf.germ V x hV (e i) = a i := by
  choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)
  have hxV : x ∈ U ⊓ Finset.univ.inf W := ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  exact ⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩

theorem germ_det [DecidableEq ι] {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U)) {x : X}
    (hx : x ∈ U) : X.presheaf.germ U x hx ((he.basis le_rfl).det v) =
      (he.stalkBasis x hx).det fun i => F.presheaf.germ U x hx (v i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  refine (RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]

  simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]
  simp only [← he.stalkBasis_apply x hx]

  rw [← map_sum, Module.Basis.repr_sum_self]
  rfl

theorem exists_isFrame_of_bijective_stalk {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U))
    {x : X} (hx : x ∈ U) (hv : Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (v i) : (F.presheaf.stalk x :)))) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame fun i => resM F h (v i) := by
  classical
  rw [bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he] at hv
  refine ⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _,
    (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩
  simp only [resM_resM]
  rw [bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)),
    ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _

end GlobalTheory.VB.Ker

namespace GlobalTheory.VB

open Ker

theorem isVB_X₁_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₂ (r + s) → IsVB S.X₃ s → IsVB S.X₁ r := by
  intro X S r s hS h₂ h₃ x
  have := hS.mono_f
  have := hS.epi_g
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  obtain ⟨U₀, b₀, hx₀, hb₀⟩ := h₂ x
  obtain ⟨U, c, hU, hx, hle, hc⟩ := h₃.exists_affine hx₀
  choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)
  have hex := (QCoh.exact_iff_stalkLinear S).1 hS.exact x
  obtain ⟨β⟩ := nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex
    (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)
  obtain ⟨V, hV, hxV, e, he⟩ := exists_germ_eq_family hx β
  have hb := (hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv
  obtain ⟨W, hW, hxW, hv⟩ := exists_isFrame_of_bijective_stalk hb
    (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by
      have := (bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β
        (fun j => S.X₂.presheaf.germ U x hx (t j)) (by
          simp only [QCoh.stalkLinear_germ, ht]
          exact hc.bijective_stalk x hx)).2 (by
          rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
            ← LinearMap.range_eq_top, Fintype.range_linearCombination]
          exact ⟨β.linearIndependent, β.span_eq⟩)
      convert this using 3
      funext k
      rcases k with i | j
      · rw [Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]
      · rw [Sum.elim_inr, Sum.elim_inr, germ_resM])
  refine ⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩
  refine (bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T)
    (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _
    (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_
  · simp only [appLinear_apply, app_resM, ht]
    exact hc T _
  · convert hv T hT using 3
    funext k
    rcases k with i | j
    · simp only [Sum.elim_inl, appLinear_apply, app_resM]
    · simp only [Sum.elim_inr, resM_resM]

end GlobalTheory.VB
end
end
