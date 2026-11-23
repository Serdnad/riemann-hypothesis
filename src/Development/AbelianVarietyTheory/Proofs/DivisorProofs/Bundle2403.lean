module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_neatPrime_levelAutSubgroup_unipotent : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  first | exact @GlobalTheory.OrbitSep.exists_neatPrime_unipAt | exact GlobalTheory.OrbitSep.exists_neatPrime_unipAt | (intros; apply GlobalTheory.OrbitSep.exists_neatPrime_unipAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

section Pull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem fnOf_pull_g (L : LB X) (J J' : (L.pull φ).ι)
    (hg : genericPoint X' ∈ (L.pull φ).U J ⊓ (L.pull φ).U J') :
    fnOf _ hg ((L.pull φ).g J J' : Γ(X', (L.pull φ).U J ⊓ (L.pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (fnOf _ (gen_mem (x := φ (genericPoint X'))
        (show φ (genericPoint X') ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) from
          ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩))
        (L.g (J PUnit.unit) (J' PUnit.unit) : Γ(X, L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)))) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact fnOf_app φ h₀ _

theorem presents_pull {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) :
    Presents (pullback φ D) (L.pull φ) (fun J => unitsMap φ (r (J PUnit.unit))) := by
  refine ⟨LB.isLB_pull h.isLB φ, fun J J' hg => ?_,
    fun J x hx => isEqn_pullback φ D (h.isEqn _ _ (mem_pull.1 hx))⟩
  rw [fnOf_pull_g φ L J J' hg]
  show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
  rw [← map_mul, ← h.isRatSec _ _ _]

end Pull

theorem genericPoint_mem_preimage {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {V : W.Opens} {y : W} (hy : y ∈ V) : genericPoint M ∈ f ⁻¹ᵁ V := by
  show f (genericPoint M) ∈ V
  have := (genericPoint_spec M).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  rw [this.eq (genericPoint_spec W)]
  exact gen_mem hy

theorem mem_sections_mul_co {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField))
    (hco : ∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x)
    {D E : CartierDiv W} {A : LB W} {rA : A.ι → W.functionFieldˣ} (hE : Presents E A rA) (t : A.Sec)
    (hP : ∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V')
      (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z)))
    {x : M.functionField} (hx : x ∈ (pullback f D).sections) (j : Fin r) :
    hE.rat t * co j x ∈ (D + E).sections := by
  refine mem_sections.2 fun y => ?_
  obtain ⟨V', hy, g, hg⟩ := D.exists_isEqn_nhds y
  have hgen := genericPoint_mem_preimage f hy
  obtain ⟨z, hz⟩ := exists_fnOf_eq hgen (f := x * GlobalTheory.functionFieldMap f g) fun m hm =>
    (isEqn_pullback f D (hg _ hm)).regularAt_iff.1 (mem_sections.1 hx m)
  obtain ⟨i, hi⟩ := exists_chart hE.isLB y
  have key := hP y i hi V' hy hgen z j
  rw [← hE.rat_mul t i (gen_mem hi), hz, mul_comm x, hco] at key
  refine ((hg y hy).add (hE.isEqn i y hi)).regularAt_iff.2 ?_
  rw [Units.val_mul]
  convert key using 1
  ring

end GlobalTheory.Cartier.PullCount

namespace GlobalTheory.Cartier.PullCount

open GlobalTheory.Cartier.DomPull GlobalTheory.Cartier.CartierDiv

theorem finrank_sections_pullback_le_mul_twist_dominant : ∀ (F : Type) [Field F] (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp F) (f : M ⟶ W) [IsDominant f], IsProjOver p → ∀ {r : ℕ} (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) → (∀ x, (∀ j, co j x = 0) → x = 0) → ∀ (A : LB W), A.IsLB → ∀ (t : A.Sec), t ≠ 0 → (∀ (y : W) (i : A.ι) (hi : y ∈ A.U i) (V' : W.Opens), y ∈ V' → ∀ (h : genericPoint M ∈ f ⁻¹ᵁ V') (z : Γ(M, f ⁻¹ᵁ V')) (j : Fin r), RegAt y (fnOf _ (gen_mem hi) (t.f i) * co j (fnOf (f ⁻¹ᵁ V') h z))) → ∀ (B : LB W), B.IsLB → (letI := algebraΓOfHom (f ≫ p); lbH0 F (B.pull f)) ≤ r * (letI := algebraΓOfHom p; lbH0 F (tens B A)) := by
  intro F _ M W _ _ p f _ hp r co hco hinj A hA t ht hP B hB
  obtain ⟨i₀, h₀⟩ := exists_chart hB (genericPoint W)
  have hD := presents_ofLB hB i₀ h₀
  obtain ⟨a₀, ha₀⟩ := exists_chart hA (genericPoint W)
  have hE := presents_ofLB hA a₀ ha₀
  have hDE := hD.tens hE
  have hpull := presents_pull f hD
  have hτ : hE.rat t ≠ 0 := fun e => ht (hE.rat_injective (e.trans (map_zero _).symm))
  letI iW : Algebra F Γ(W, ⊤) := algebraΓOfHom p
  letI iM : Algebra F Γ(M, ⊤) := algebraΓOfHom (f ≫ p)
  letI : Module F (B.pull f).Sec := Module.compHom _ (algebraMap F Γ(M, ⊤))
  haveI : IsScalarTower F Γ(M, ⊤) (B.pull f).Sec := IsScalarTower.of_compHom _ _ _
  letI : Module F (tens B A).Sec := Module.compHom _ (algebraMap F Γ(W, ⊤))
  haveI : IsScalarTower F Γ(W, ⊤) (tens B A).Sec := IsScalarTower.of_compHom _ _ _
  haveI : Module.Finite F (tens B A).Sec := by
    have := finite_coh_zero_twist_of_isProjOver (f := p) (fun _ => rfl) hp (isLB_tens hB hA)
    exact .equiv ((cohZeroTwistEquiv (tens B A)).restrictScalars F)
  have eW (c : F) : algebraMap F Γ(W, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ c := by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have eM (c : F) : algebraMap F Γ(M, ⊤) c = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (f ≫ p) ⊤ c := by
    change (f ≫ p).appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hconst (c : F) : fnOf ⊤ trivial (algebraMap F Γ(M, ⊤) c) =
      GlobalTheory.functionFieldMap f (fnOf ⊤ trivial (algebraMap F Γ(W, ⊤) c)) := by
    rw [eM, eW]
    exact (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) c).symm
  let Ψj (j : Fin r) : (B.pull f).Sec →ₗ[F] (tens B A).Sec :=
    { toFun := fun s => hDE.secEquiv.symm
        ⟨hE.rat t * co j (hpull.rat s), mem_sections_mul_co f co hco hE t hP (hpull.rat_mem s) j⟩
      map_add' := fun s s' => by
        rw [← map_add (f := _)]
        congr 1
        apply Subtype.ext
        simp only [map_add (f := _), mul_add, Submodule.coe_add]
      map_smul' := fun c s => by
        rw [RingHom.id_apply]
        change _ = algebraMap F Γ(W, ⊤) c • (_ : (tens B A).Sec)
        rw [← map_smul]
        congr 1
        apply Subtype.ext
        change hE.rat t * co j (hpull.rat (algebraMap F Γ(M, ⊤) c • s)) =
          algebraMap F Γ(W, ⊤) c • (hE.rat t * co j (hpull.rat s))
        rw [map_smul, Algebra.smul_def, Algebra.smul_def, algebraMap_top, algebraMap_top, hconst, hco,
          mul_left_comm] }
  let Ψ : (B.pull f).Sec →ₗ[F] (Fin r → (tens B A).Sec) := LinearMap.pi Ψj
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun s hs => ?_
    refine hpull.rat_injective ((hinj _ fun j => ?_).trans (map_zero _).symm)
    have e := congrArg (fun v => (hDE.secEquiv (v j) : W.functionField)) hs
    simp only [Ψ, Ψj, LinearMap.pi_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
      Pi.zero_apply, map_zero, ZeroMemClass.coe_zero] at e
    exact (mul_eq_zero.1 e).resolve_left hτ
  rw [lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_eq_finrank]
  calc Module.finrank F (B.pull f).Sec ≤ Module.finrank F (Fin r → (tens B A).Sec) :=
        LinearMap.finrank_le_finrank_of_injective hΨ
    _ = r * Module.finrank F (tens B A).Sec := by
        rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end GlobalTheory.Cartier.PullCount
end
end

section

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.DefRead.Transport

section General

variable {Ks LL WL C : Type} [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Algebra Ks ℂ] [Algebra LL ℂ] [IsScalarTower Ks LL ℂ]

def phiBil (e : C →ₗ[Ks] WL) : ℂ →+ C →+ ℂ ⊗[LL] WL :=
  AddMonoidHom.mk' (fun z => ((TensorProduct.mk LL ℂ WL z).toAddMonoidHom.comp e.toAddMonoidHom))
    (fun a b => by ext f; exact TensorProduct.add_tmul a b (e f))

theorem phiBil_compat (e : C →ₗ[Ks] WL) (r : Ks) (z : ℂ) (f : C) :
    phiBil (LL := LL) e (r • z) f = phiBil (LL := LL) e z (r • f) := by
  show (r • z) ⊗ₜ[LL] e f = z ⊗ₜ[LL] e (r • f)
  rw [map_smul, ← algebraMap_smul LL r (e f), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    algebraMap_smul LL r z]

def phi (e : C →ₗ[Ks] WL) : ℂ ⊗[Ks] C →ₗ[ℂ] ℂ ⊗[LL] WL where
  toFun := TensorProduct.liftAddHom (phiBil (LL := LL) e) (phiBil_compat e)
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul z f =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul]
      show (c • z) ⊗ₜ[LL] e f = c • (z ⊗ₜ[LL] e f)
      rw [TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

@[simp] theorem phi_tmul (e : C →ₗ[Ks] WL) (z : ℂ) (f : C) : phi e (z ⊗ₜ[Ks] f) = z ⊗ₜ[LL] e f :=
  TensorProduct.liftAddHom_tmul (phiBil (LL := LL) e) (phiBil_compat e) z f

theorem phi_comm (e : C →ₗ[Ks] WL) (a : C →ₗ[Ks] C) (r : WL →ₗ[LL] WL) (h : ∀ f, e (a f) = r (e f)) :
    phi e ∘ₗ a.baseChange ℂ = r.baseChange ℂ ∘ₗ phi e := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z f => simp [h]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]

theorem phi_bijective (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) :
    Function.Bijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap)) := by
  let bW : Module.Basis (Fin n) Ks (Submodule.span Ks (Set.range b)) := Module.Basis.span hliK
  let bK : Module.Basis (Fin n) Ks WK := bW.map (LinearEquiv.ofEq _ _ hspK)
  let bC : Module.Basis (Fin n) Ks C := bK.map e.symm
  let bL : Module.Basis (Fin n) LL WL := Module.Basis.mk hliL (by rw [hspL])
  let cC := Algebra.TensorProduct.basis ℂ bC
  let cL := Algebra.TensorProduct.basis ℂ bL
  have key : phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) = (cC.equiv cL (Equiv.refl _)).toLinearMap := by
    refine cC.ext fun j => ?_
    show _ = (cC.equiv cL (Equiv.refl _)) (cC j)
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
    simp [cC, cL, bC, bK, bW, bL, Module.Basis.span_apply]
  rw [key]
  exact (cC.equiv cL (Equiv.refl _)).bijective

theorem transport_general {H G X : Type} [Group G] [Group H] [DecidableEq X] [MulAction H X]
    (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL) (hliK : LinearIndependent Ks b)
    (hspK : Submodule.span Ks (Set.range b) = WK) (hliL : LinearIndependent LL b)
    (hspL : Submodule.span LL (Set.range b) = ⊤) (e : C ≃ₗ[Ks] WK) (ρ0 : G → (WL →ₗ[LL] WL))
    (act : G → C →ₗ[Ks] C) (he : ∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) (s : G → ℂ) (φ : H →* G)
    (A : X → Submodule ℂ (ℂ ⊗[Ks] C)) (hA : DirectSum.IsInternal A)
    (hinv : ∀ (h : H) (y : X), ∀ v ∈ A y, (act (φ h)).baseChange ℂ v ∈ A (h • y)) :
    ∃ A' : X → Submodule ℂ (ℂ ⊗[LL] WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, (s (φ h) • (ρ0 (φ h)).baseChange ℂ) v ∈ A' (h • y) := by
  let Ψ := LinearEquiv.ofBijective (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap))
    (phi_bijective WK n b hliK hspK hliL hspL e)
  let o := Submodule.orderIsoMapComap Ψ
  refine ⟨fun y => o (A y), ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hA ⊢
    refine ⟨iSupIndep.map_orderIso o hA.1, ?_⟩
    rw [← o.map_iSup, hA.2, o.map_top]
  · intro h y v hv
    obtain ⟨u, hu, rfl⟩ := (Submodule.mem_map).1 hv
    have hc := LinearMap.congr_fun (phi_comm (WK.subtype ∘ₗ e.toLinearMap) (act (φ h)) (ρ0 (φ h))
      (fun f => he _ f)) u
    refine Submodule.mem_map.2 ⟨s (φ h) • (act (φ h)).baseChange ℂ u, (A (h • y)).smul_mem _ (hinv h y u hu), ?_⟩
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.smul_apply, map_smul]
    show s (φ h) • phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) _ = s (φ h) • (ρ0 (φ h)).baseChange ℂ (phi (LL := LL) (WK.subtype ∘ₗ e.toLinearMap) u)
    rw [hc]

end General


open GlobalTheory.DefRead in
theorem transport : ∀ (Ks LL WL C H G X : Type) [Field Ks] [Field LL] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [AddCommGroup C] [Module Ks C] [Group G] [Group H] [Fintype X] [DecidableEq X] [MulAction H X]
    (σ : LL →+* ℂ) (WK : Submodule Ks WL) (n : ℕ) (b : Fin n → WL), (∀ j, b j ∈ WK) → LinearIndependent Ks b →
    Submodule.span Ks (Set.range b) = WK → LinearIndependent LL b → Submodule.span LL (Set.range b) = ⊤ →
    ∀ (e : C ≃ₗ[Ks] WK) (ρ0 : G →* (WL →ₗ[LL] WL)) (χ : G →* LLˣ) (act : G → C →ₗ[Ks] C),
    (∀ g f, ((e (act g f) : WK) : WL) = ρ0 g (e f)) → ∀ (φ : H →* G) (A : X → Submodule ℂ (GlobalTheory.DefRead.VC (σ.comp (algebraMap Ks LL)) C)),
    DirectSum.IsInternal A → (∀ (h : H) (y : X), ∀ v ∈ A y, GlobalTheory.DefRead.bcLin (σ.comp (algebraMap Ks LL)) (act (φ h)) v ∈ A (h • y)) →
    ∃ A' : X → Submodule ℂ (GlobalTheory.DefRead.VC σ WL), DirectSum.IsInternal A' ∧
      ∀ (h : H) (y : X), ∀ v ∈ A' y, GlobalTheory.DefRead.twBC σ ρ0 χ (φ h) v ∈ A' (h • y) := by
  intro Ks LL WL C H G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ WK n b _ hliK hspK hliL hspL e ρ0 χ act he φ A hA hinv
  letI : Algebra Ks ℂ := (σ.comp (algebraMap Ks LL)).toAlgebra
  letI : Algebra LL ℂ := σ.toAlgebra
  haveI : IsScalarTower Ks LL ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨A', h1, h2⟩ := transport_general (X := X) WK n b hliK hspK hliL hspL e (fun g => ρ0 g) act he
    (fun g => σ (((χ g)⁻¹ : LLˣ) : LL)) φ A hA hinv
  exact ⟨A', h1, fun h y v hv => by rw [twBC_apply]; exact h2 h y v hv⟩

end GlobalTheory.DefRead.Transport
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.boundary_germ_snc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1), x ∉ (j₀ TF.Y Z).opensRange → IsRegularLocalRing ((X₀ TF.Y Z).presheaf.stalk x) ∧ ∃ (n : ℕ) (f : Fin n → (X₀ TF.Y Z).presheaf.stalk x) (J : Finset (Fin n)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp ((X₀ TF.Y Z).presheaf.stalk x) n f ∧ J.Nonempty ∧ Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) = Ideal.span {∏ i ∈ J, f i} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx hnot
  classical
  obtain ⟨hreg, V, hyV, n, f', J, hrsp, hV⟩ := TF.snc ((barComp TF.Y Z).ι x)
  let φ : TF.Y.X.presheaf.stalk ((barComp TF.Y Z).ι x) ≃+* (X₀ TF.Y Z).presheaf.stalk x :=
    (asIso ((barComp TF.Y Z).ι.stalkMap x)).commRingCatIsoToRingEquiv
  have hφ : ∀ a, φ a = ((barComp TF.Y Z).ι.stalkMap x).hom a := fun _ => rfl
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, n, fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i)), J, ?_, ?_, ?_⟩
  · obtain ⟨hspan, hdim⟩ := hrsp
    refine ⟨?_, hdim.trans (ringKrullDim_eq_of_ringEquiv φ)⟩
    have hr : Set.range (fun i => φ (TF.Y.X.presheaf.germ V.1 _ hyV (f' i))) =
        φ '' Set.range (fun i => TF.Y.X.presheaf.germ V.1 _ hyV (f' i)) := Set.range_comp _ _
    rw [hr, ← Ideal.map_span, hspan]
    exact (IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ))
  · rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hnot
    rw [Finset.prod_empty, Ideal.span_singleton_one] at hV
    have hst : ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x) = ⊤ := by
      rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hV, Ideal.map_top]
    have hns := (ReciprocityTheory.AnForm.R.mem_support_iff_stalkId (LogKS.boundary TF.Y) ((barComp TF.Y Z).ι x)).not.mpr
      (not_not.mpr hst)
    rw [LogKS.boundary, Scheme.IdealSheafData.coe_support_vanishingIdeal] at hns
    have hin : (barComp TF.Y Z).ι x ∈ LogKS.interior TF.Y := by
      simpa using hns
    rw [LogKS.interior] at hin
    obtain ⟨z, hz⟩ := hin
    have hzB : z ∈ TF.Y.j ⁻¹ᵁ barComp TF.Y Z := by
      show TF.Y.j z ∈ barComp TF.Y Z
      rw [hz]; first | exact x.2 | simp | exact (barComp TF.Y Z).range_ι.le ⟨x, rfl⟩
    refine ⟨⟨z, hzB⟩, (barComp TF.Y Z).ι.isOpenEmbedding.injective ?_⟩
    have h2 := congrArg (fun f => f.base ⟨z, hzB⟩) (j₀_ι TF.Y Z)
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    first | exact h2.trans hz | (refine Eq.trans ?_ hz; exact h2) | (rw [Scheme.Hom.comp_apply] at h2; exact h2.trans hz)
  · have e1 : Ideal.map (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx)
        ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U) =
        Ideal.map φ.toRingHom (Ideal.map (TF.Y.X.presheaf.germ U.1 _ hx).hom
          ((Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal U)) := by
      rw [Ideal.map_map]
      congr 1
      ext r
      simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hφ]
      rw [Scheme.Hom.germ_stalkMap_apply]
    have hVb : (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl).ideal V =
        Ideal.span {∏ i ∈ J, f' i} := hV
    rw [e1, ← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ U _ hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map _ V _ hyV, hVb,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_prod]
    rw [map_prod]
    rfl
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv.Spread'

theorem germ_pt' {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) {U : X.Opens} (hU : IsAffineOpen U)
    (hy : B.ι y ∈ U) :
    spMap (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y).hom ≫ hU.fromSpec = B.toScheme.fromSpecStalk y ≫ B.ι := by
  show Spec.map (X.presheaf.germ U (B.ι y) hy ≫ B.ι.stalkMap y) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.LogKSDiv.Spread'

set_option autoImplicit false

theorem GlobalTheory.LogKSDiv.chartRestr_eq_germ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hx ρ hρ r
  have hη : (barComp TF.Y Z).ι (genericPoint (X₀ TF.Y Z)) ∈ U.1 := by
    have h := (genericPoint_spec (X₀ TF.Y Z)).mem_open_set_iff ((barComp TF.Y Z).ι ⁻¹ᵁ U.1).isOpen
    exact h.2 ⟨x, trivial, hx⟩
  set ψ := (TF.Y.X.presheaf.germ U.1 _ hη ≫ (barComp TF.Y Z).ι.stalkMap (genericPoint (X₀ TF.Y Z))).hom with hψ
  have hg := GlobalTheory.LogKSDiv.Spread'.germ_pt' (barComp TF.Y Z) (genericPoint (X₀ TF.Y Z)) U.2 hη
  have hmono : Mono (LogKS.chart U) := by
    unfold LogKS.chart
    have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    infer_instance
  have e1 : spMap ρ = spMap ψ := by
    rw [← cancel_mono (LogKS.chart U), hρ]
    exact hg.symm
  have e2 : ρ = ψ := by
    have := Spec.map_injective e1
    exact congrArg CommRingCat.Hom.hom this
  rw [e2, hψ, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.germ_stalkMap_apply]
  simp only [GlobalTheory.LogKSDiv.stalkHom, RingHom.comp_apply, RingHom.algebraMap_toAlgebra]
  change _ = ((X₀ TF.Y Z).presheaf.germ _ x hx ≫ (X₀ TF.Y Z).presheaf.stalkSpecializes _).hom _
  erw [TopCat.Presheaf.germ_stalkSpecializes]
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory.LogKSDiv

theorem topPair_change_matrix : ∀ {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) {n : ℕ}
    (D D' : Fin n → (letI := α.toAlgebra; Derivation k A A)) (L : Matrix (Fin n) (Fin n) A),
    (letI := α.toAlgebra; ∀ j, D j = ∑ i, L i j • D' i) →
    ∀ η, GlobalTheory.LogKSDiv.topPair α D η = L.det * GlobalTheory.LogKSDiv.topPair α D' η := by
  intro k A _ _ α n D D' L hD η
  letI := α.toAlgebra
  have key : (Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j)) :
        (Ω[A⁄k]) [⋀^Fin n]→ₗ[A] A) =
      L.det • Matrix.detRowAlternating.compLinearMap
      (LinearMap.pi fun j => (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j)) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    change Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D j) (v i)) =
      L.det * Matrix.det (Matrix.of fun i j =>
        (KaehlerDifferential.linearMapEquivDerivation k A).symm (D' j) (v i))
    rw [mul_comm, ← Matrix.det_mul]
    congr 1
    ext i j

    simp only [Matrix.of_apply, Matrix.mul_apply, hD j, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  show (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η = L.det * (exteriorPower.alternatingMapLinearEquiv _ : _ →ₗ[A] A) η
  rw [key, map_smul, LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.LogKSDiv
end
