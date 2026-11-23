module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightShiftEqDetMul
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb

namespace GlobalTheory.PullCocycle

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]

theorem formula_span (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka))
    (a : U → C → ℂˣ)
    (ha : ∀ (h : U) (F : C → Frame M.Ψ r → ℂ) (hF : F ∈ M.SS ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ ⟨M.res F, Submodule.subset_span ⟨F, hF, rfl⟩⟩ : M.cusp ka) : C → M.dom → ℂ) c x =
        (a h c : ℂ) * M.pull h F c x.1)
    (h : U) (c : C) (x : M.dom) (g : C → M.dom → ℂ) (hg : g ∈ Submodule.span ℂ (M.res '' M.SS ka)) :
    ((ρ h⁻¹ ⟨g, hg⟩ : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * g (h • c) (Lmap M h c x) := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact ha h F hF c x
  | zero =>
    show ((ρ h⁻¹ 0 : M.cusp ka) : C → M.dom → ℂ) c x = _
    simp
  | add y z hy hz ihy ihz =>
    show ((ρ h⁻¹ ((⟨y, hy⟩ : M.cusp ka) + ⟨z, hz⟩) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_add (f := _), Submodule.coe_add, Pi.add_apply, Pi.add_apply, ihy, ihz]
    simp [mul_add]
  | smul t y hy ih =>
    show ((ρ h⁻¹ (t • (⟨y, hy⟩ : M.cusp ka)) : M.cusp ka) : C → M.dom → ℂ) c x = _
    rw [map_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, ih]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem rho_inv_rho (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (h : U)
    (f : M.cusp ka) : ρ h⁻¹ (ρ h f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem pull_mul_eq (M : TwoLevels E r U C) (f : C → M.dom → ℂ) (hf : IsInv M f) (g h : U) (c : C) (x : M.dom) :
    f ((h * g) • c) (Lmap M (h * g) c x) = f (h • g • c) (Lmap M h (g • c) (Lmap M g c x)) := by
  set γ := M.tr (h * g) c * (M.tr h (g • c) * M.tr g c)⁻¹ with hγdef
  have hγ : γ ∈ (M.comp ((h * g) • c)).Γ := M.tr_mul h g c
  have e : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 = (Lmap M (h * g) c x).1 := by
    show lact γ (lact (M.tr h (g • c)) (lact (M.tr g c) x.1)) = lact (M.tr (h * g) c) x.1
    rw [← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul (M.tr h (g • c)) (M.tr g c),
      ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul γ, hγdef, inv_mul_cancel_right]
  have hx : lact γ (Lmap M h (g • c) (Lmap M g c x)).1 ∈ M.dom := e ▸ (Lmap M (h * g) c x).2
  have := hf ((h * g) • c) γ hγ (Lmap M h (g • c) (Lmap M g c x)) hx
  have e2 : (⟨lact γ (Lmap M h (g • c) (Lmap M g c x)).1, hx⟩ : M.dom) = Lmap M (h * g) c x := Subtype.ext e
  rw [e2] at this
  rw [this, mul_smul]

theorem exists_cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → (∀ f ∈ M.cusp ka, IsInv M f) → ∃ a : U → C → ℂˣ, (∀ (g h : U) (c : C), a (h * g) c = a g c * a h (g • c)) ∧ ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom), ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
  intro E _ _ _ r U C _ _ M ka ρ hρ hinv
  obtain ⟨a, ha⟩ := hρ
  have hform : ∀ (h : U) (f : M.cusp ka) (c : C) (x : M.dom),
      ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = (a h c : ℂ) * (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) := by
    rintro h ⟨g, hg⟩ c x
    exact formula_span M ka ρ a ha h c x g hg
  classical
  let C0 : C → Prop := fun c => ∃ f : M.cusp ka, ∃ x : M.dom, (f : C → M.dom → ℂ) c x ≠ 0
  have hstab : ∀ (h : U) (c : C), C0 c → C0 (h • c) := by
    rintro h c ⟨f, x, hfx⟩
    refine ⟨ρ h f, Lmap M h c x, fun h0 => hfx ?_⟩
    calc (f : C → M.dom → ℂ) c x = ((ρ h⁻¹ (ρ h f) : M.cusp ka) : C → M.dom → ℂ) c x := by
          rw [rho_inv_rho]
      _ = (a h c : ℂ) * ((ρ h f : M.cusp ka) : C → M.dom → ℂ) (h • c) (Lmap M h c x) := hform h _ c x
      _ = 0 := by rw [h0, mul_zero]
  have hstab' : ∀ (h : U) (c : C), ¬ C0 c → ¬ C0 (h • c) := fun h c hc h1 => hc (by
    have := hstab h⁻¹ (h • c) h1
    rwa [inv_smul_smul] at this)
  have hcoc : ∀ (g h : U) (c : C) (x : M.dom) (f : M.cusp ka),
      (a (h * g) c : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) =
        (a g c : ℂ) * (a h (g • c) : ℂ) * (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) := by
    intro g h c x f
    have L := hform (h * g) f c x
    have R : ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x =
        (a g c : ℂ) * ((a h (g • c) : ℂ) * (f : C → M.dom → ℂ) (h • g • c) (Lmap M h (g • c) (Lmap M g c x))) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hform g, hform h]
    rw [← L, R, pull_mul_eq M _ (hinv _ f.2) g h c x]
    ring
  refine ⟨fun h c => if C0 c then a h c else 1, ?_, ?_⟩
  · intro g h c
    by_cases hc : C0 c
    · have hgc : C0 (g • c) := hstab g c hc
      have hhgc : C0 ((h * g) • c) := hstab (h * g) c hc
      simp only [hc, hgc, if_true]
      obtain ⟨f', x, hfx⟩ := hc
      set f := ρ (h * g) f' with hfdef
      have hV : (f : C → M.dom → ℂ) ((h * g) • c) (Lmap M (h * g) c x) ≠ 0 := by
        intro h0
        apply hfx
        calc (f' : C → M.dom → ℂ) c x = ((ρ (h * g)⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x := by
              rw [hfdef, rho_inv_rho]
          _ = 0 := by rw [hform, h0, mul_zero]
      ext
      push_cast
      exact mul_right_cancel₀ hV (hcoc g h c x f)
    · have hgc : ¬ C0 (g • c) := hstab' g c hc
      simp [hc, hgc]
  · intro h f c x
    by_cases hc : C0 c
    · simp only [hc, if_true]
      exact hform h f c x
    · have hhc : ¬ C0 (h • c) := hstab' h c hc
      simp only [hc, if_false, Units.val_one, one_mul]
      have l0 : ((ρ h⁻¹ f : M.cusp ka) : C → M.dom → ℂ) c x = 0 := by
        by_contra hne
        exact hc ⟨ρ h⁻¹ f, x, hne⟩
      have r0 : (f : C → M.dom → ℂ) (h • c) (Lmap M h c x) = 0 := by
        by_contra hne
        exact hhc ⟨f, _, hne⟩
      rw [l0, r0]

end GlobalTheory.PullCocycle

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SumExpAt

theorem mem_locP {R : Type} [CommRing R] {W : Type} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (L : Submodule R W) (x : W) : x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

theorem locIncl_of_equiv {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (e : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (N D : Submodule (𝓞 K) V) (N' D' : Submodule (𝓞 K) V')
    (hN : N.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = N')
    (hD : D.map ((e : V →ₗ[K] V').restrictScalars (𝓞 K)) = D')
    (h : ∀ x ∈ N', a • x ∈ Formalism.HermitianLatticesTheory.localization₂ p D') : ∀ v ∈ N, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p D := by
  intro v hv
  set f : V →ₗ[𝓞 K] V' := (e : V →ₗ[K] V').restrictScalars (𝓞 K) with hf
  have hx : f v ∈ N' := hN ▸ Submodule.mem_map_of_mem hv
  obtain ⟨s, hs, hsD⟩ := (mem_locP p D' _).1 (h _ hx)
  refine (mem_locP p D _).2 ⟨s, hs, ?_⟩
  rw [← hD] at hsD
  obtain ⟨y, hy, hye⟩ := hsD
  have hinj : Function.Injective f := e.injective
  have : y = s • a • v := hinj (by rw [hye, map_smul, map_smul])
  rw [← this]
  exact hy

theorem cutLat_locIncl {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.DIV.CSD K) {d : ℕ}
    (E : Matrix (Fin S.dim) (Fin d) K) (p : Ideal (𝓞 K)) [p.IsPrime] (a : 𝓞 K)
    (h : ∀ c, ∀ v ∈ S.Nab c, a • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (S.Del c)) :
    ∀ z ∈ Formalism.DivisionValues.cutLat E S.nabLat, a • z ∈ Formalism.HermitianLatticesTheory.localization₂ p (Formalism.DivisionValues.cutLat E S.delLat) := by
  classical
  intro z hz
  have hz' : ∀ c, S.I (E.mulVec z) c ∈ S.Nab c := fun c => hz c (Set.mem_univ c)
  have hlin : ∀ (r : 𝓞 K) (y : Fin d → K), S.I (E.mulVec (r • y)) = r • S.I (E.mulVec y) := fun r y => by
    have h1 := ((Matrix.mulVecLin E).restrictScalars (𝓞 K)).map_smul r y
    have h2 := (S.I.restrictScalars (𝓞 K)).map_smul r (E.mulVec y)
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at h1 h2
    rw [h1, h2]
  choose s hs hsD using fun c => (mem_locP p (S.Del c) _).1 (h c _ (hz' c))
  refine (mem_locP p _ _).2 ⟨∏ c, s c, prod_mem fun c _ => hs c, ?_⟩
  intro c _
  show S.I (E.mulVec ((∏ c, s c) • a • z)) c ∈ S.Del c
  rw [hlin, hlin, ← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ c), Pi.smul_apply, Pi.smul_apply, mul_comm,
    mul_smul]
  exact Submodule.smul_mem _ _ (hsD c)

end GlobalTheory.SumExpAt

namespace GlobalTheory.SumExpAt


open Formalism.CohomologicalDescent.LD in
theorem exZ_res_eq_natW (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) (f : ℕ → ℕ) (c : ℤ)
    (hc : ∀ a : Fin n, (f a : ℤ) = lam.w a + c) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl (res n f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl lam.natW l := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · congr 1
    funext a
    exact a.elim0
  · let m : Fin n := ⟨n - 1, by omega⟩
    have hds : lam.detShift = lam.w m := by
      simp only [Formalism.BasicNotions.DomWeight.detShift, dif_pos hn]
      rfl
    have hres : res n f = fun a => lam.natW a + f m := by
      funext a
      have h1 := hc a
      have h2 := hc m
      have h3 : lam.w m ≤ lam.w a := lam.anti (Fin.le_def.2 (by simp only [m]; omega))
      have h4 : ((lam.w a - lam.w m).toNat : ℤ) = lam.w a - lam.w m := Int.toNat_of_nonneg (by omega)
      change f a.val = (lam.w a - lam.detShift).toNat + f m
      rw [hds]
      omega
    have hanti : Antitone lam.natW := fun i j hij => by
      have := lam.anti hij
      exact Int.toNat_le_toNat (by omega)
    rw [hres]
    exact Formalism.CohomologicalDescent.LA.exact_z_twist_by_det n lam.natW (f m) l hanti hl

theorem exZ_res_congr {N n : ℕ} (h : N = n) (f : ℕ → ℕ) (l : ℕ) :
    Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Formalism.CohomologicalDescent.LD.res N f) l = Formalism.CohomologicalDescent.LA.exZ n n le_rfl (Formalism.CohomologicalDescent.LD.res n f) l := by
  subst h
  rfl

end GlobalTheory.SumExpAt

namespace GlobalTheory.ExpTie

open GlobalTheory.SumExpAt
open Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem lIncl_sumExp (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (hD : Dict L j P W) (t : p.P.T)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    LIncl (blk p j t) (lvlL p) (subZ p j t) w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := p.charW.base.fam.tie
  obtain ⟨e, -, -, -, hNab, hDel⟩ := hT.coefL j t
  have hJ : W.JA P (Formalism.EigenvalueLevelCeiling.plc w) = ∑ τ, Formalism.CohomologicalDescent.LA.exZ (Vc D j).rank (Vc D j).rank le_rfl
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ).natW (Formalism.EigenvalueLevelCeiling.plc w) := by
    unfold Wts.JA Wts.ex
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [exZ_res_congr hD.Nr]
    obtain ⟨c, hc⟩ := hD.lam τ
    exact exZ_res_eq_natW _ _ _ c hc _ (Formalism.EigenvalueLevelCeiling.plc_prime w)
  intro z hz
  rw [hJ]
  refine cutLat_locIncl (blk p j t).S _ w.asIdeal _ (fun c => ?_) z hz
  refine locIncl_of_equiv e w.asIdeal _ _ _ _ _ (hNab c) (hDel c) ?_
  have hLat (g : Bridge.Gf (Vc D j)) : Submodule.IsFullLattice D.host.E (Bridge.hLat (Vc D j) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D j).rank (GlobalTheory.Member.latC (Vc D j)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D j) g).trans hΛ.symm)]
    exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E h1, span_eq_top := h2 }
  exact GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr _ _ _ _ _ _ _ (hLat _) w

end Point

end GlobalTheory.ExpTie

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : _root_.GlobalTheory.RealIndexBound.RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → _root_.GlobalTheory.RealIndexBound.RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}

theorem card_comap_base (h1 : R.grp_levels F) : Nat.card (F.P0.comap (mirIncl R)) = Nat.card F.P0 := by
  refine Nat.card_congr (Equiv.ofBijective (fun u : F.P0.comap (mirIncl R) => (⟨mirIncl R u, u.2⟩ : F.P0)) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (mirIncl_injective R (congrArg Subtype.val hab))
  · rintro ⟨g, hg⟩
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨⟨u, hg⟩, rfl⟩

variable {P : Type} [Group P] [Finite P]

theorem mem_eig_iff {O : OnObj ((R.toCx F).data F.cr false) P c} {inc : P →* G} (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (hinc : F.P0 ≤ inc.range) (j : Fin D.R.m) (w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL))
    (hρ : ∀ g x, w (O.ρ j g x) = (R.FW j).ρ (inc g) (w x)) (hU : O.U = F.P0.comap inc)
    (hψ : ∀ (g : P) (hg : inc g ∈ F.P0), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ))
    (x : Fin (O.nZ j) → D.what₂.LL) : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ w x ∈ GlobalTheory.CovTop.spType R F j := by
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ ∀ u : O.U, O.ρ j u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ j g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW j).ρ (inc g) (w x) = (((R.FW j).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • w x :=
    fun g hg => by
      rw [chi_eq_one h1 h2 j hg, one_mul, ← hψ g hg, ← hρ, ← LinearEquiv.map_smul, w.injective.eq_iff]
  show _ ↔ ∀ q : F.P0, (R.FW j).ρ q (w x) = (((R.FW j).chi q * F.ψ0⁻¹ q : D.what₂.LLˣ) : D.what₂.LL) • w x
  refine e1.trans ⟨?_, fun h u => ?_⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨q, rfl⟩ := hinc hg
    exact (e2 q hg).1 (h ⟨q, hU ▸ hg⟩)
  · have hg : inc u ∈ F.P0 := (hU ▸ u.2 : (u : P) ∈ F.P0.comap inc)
    exact (e2 u hg).2 (h ⟨inc u, hg⟩)

theorem tied_dims {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O) (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (j : Fin D.R.m) :
    O.nZ j = R.nW j ∧ Nat.card O.U = Nat.card F.P0 ∧ O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType R F j) : ℝ) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v, -⟩ := exists_place3 D.what₂.LL
  have t := (ht v j).1
  let w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
    LinearEquiv.ofBijective (toForms (T := (run v).full) (R := R) (h v) fw j (z j))
      (toForms_bijective (T := (run v).full) (R := R) (h v) fw j (z j))
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have := w.finrank_eq
    simpa only [Module.finrank_fin_fun] using this
  · rw [t.U_eq]
    exact card_comap_base h1
  · have hm : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).map (w : (Fin (O.nZ j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)) =
        GlobalTheory.CovTop.spType R F j := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq x).1 hx
      · intro hu
        refine ⟨w.symm u, ?_, w.apply_symm_apply u⟩
        refine (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq _).2 ?_
        rw [w.apply_symm_apply]
        exact hu
    unfold OnObj.d0
    rw [← hm, LinearEquiv.finrank_map_eq]

end Tied

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem leafShareI_of_shareW (p : PtAt ex Csz) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hR : RecAt p Tp r O) (hW : ∀ i, ShareW p i (1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3))) :
    LeafShareI O := by
  have hfk : O.f = (D.R.f : ℝ) ∧ O.k = (D.R.k : ℝ) := by
    letI := hostAlg D
    obtain ⟨st, rt⟩ := hR.1.depth
    exact ⟨rt.f_eq, rt.k_eq⟩
  obtain ⟨hc, hinj, ht⟩ := hR.1.tied
  intro j
  obtain ⟨hn, hU, hd⟩ := tied_dims ht p.charW.base.grp.levels p.charW.base.grp.chiW j
  refine ⟨O.y, le_rfl, ?_⟩
  have hy : O.y = 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) := by
    unfold OnObj.y
    rw [hfk.1, hfk.2]
  have hw := hW j
  unfold ShareW at hw
  rw [hy, hn, hd, hU]
  exact hw

end Point

end GlobalTheory.ShareOn.Comparison₂

namespace GlobalTheory.ShareOn

end GlobalTheory.ShareOn
end
end

section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

namespace GlobalTheory.CovTop.FromComp

theorem core (ι : Type) [Finite ι] [Nonempty ι] (T D A cs X cc z ρ R Bn δ' E C1 C2 mu : ℝ) (h sl δ dc degc : ι → ℝ)
    (hD : 0 ≤ D) (hT : 3 * D + 5 ≤ T) (hA : 0 < A) (hcs : 0 ≤ cs) (hX : 0 ≤ X) (hcc : 0 ≤ cc) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R) (hBn : 0 < Bn) (hδ : 0 < δ') (hE : 1 ≤ E)
    (h1 : ∀ c, δ' ≤ δ c ∧ δ c ≤ δ' / (1 - ρ)) (h2 : ∀ c, Bn * δ c ≤ dc c ∧ (1 - z) * dc c ≤ Bn * δ c)
    (h3 : ∀ c, 0 ≤ h c + cs) (h4 : ∀ c, (1 - ρ) * max 0 (sl c + cs) ≤ h c + cs + cc)
    (h5 : -X ≤ (∑ᶠ c, sl c) / (Nat.card ι : ℝ))
    (h6 : ∀ c, Bn * δ c * (T * h c - 3 * (D + 1) * |h c| - A * Real.log (2 + |h c|) - R) ≤ degc c)
    (h7 : T * X ≤ C1 * E) (h8 : T * cc ≤ C1 * E) (h9 : cs * (6 * D + 10 + T * (z + 2 * ρ)) ≤ C1 * E)
    (h10 : A * Real.log (max A 1) + R ≤ C2 * E)
    (h11 : 2 * ((∑ᶠ c, degc c) / ∑ᶠ c, dc c) ≤ mu) : -((2 * (3 * C1 + C2 + 4)) * E) ≤ mu := by
  letI := Fintype.ofFinite ι
  rw [finsum_eq_sum_of_fintype] at h5
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at h11
  rw [Nat.card_eq_fintype_card] at h5
  have := Formalism.ExtensionFiltration.mean_height_sum_bound ι T D A cs X cc z ρ R 0 Bn δ' h sl δ dc degc 0 0 (4 * ((3 * C1 + C2 + 4) * E)) 0 0 0
    (C1 * E) (C1 * E) mu hD hT hA hcs hX hcc hz0 hz1 hρ0 hρ1 hR le_rfl hBn hδ h1 h2 h3 h4 h5
    (fun c => by simpa using h6 c) (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem atPoint (Y : Cov p i) (PP A C1 C2 : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hg : DeepGoodAt p i Y) (hs : SizeAt p i PP A)
    (hd : ∀ u1, Quo p i PP u1 → DegAt p i Y u1) (hsh : ∀ u1, Quo p i PP u1 → ShareAt p i Y PP u1)
    (hh : ∀ u1, Quo p i PP u1 → HeightAt p i Y PP C1 u1) (hhs : ∀ u1, Quo p i PP u1 → HSAt p i Y PP C2 u1)
    (hsum : SumAt p i Y) : UAt p i Y (2 * (3 * C1 + C2 + 4)) := by
  obtain ⟨-, -, -, -, -, hfin, hne, -⟩ := hg
  obtain ⟨hb1, hbE, -, -, -, -, hq⟩ := hs
  obtain ⟨⟨u1, hu⟩, hq⟩ := hq hi
  obtain ⟨hTD, hρ0, hρ1, hz1⟩ := hq u1 hu
  obtain ⟨δ', hδ, h1⟩ := hd u1 hu
  obtain ⟨cs, cc, X, sl, hcs, hcc, hX, h3, h4, h5, h7, h8, h9⟩ := hh u1 hu
  obtain ⟨B, R, hB, hR, h10, h6⟩ := hhs u1 hu
  have hz0 : 0 ≤ zed p i PP u1 := by
    unfold zed
    positivity
  have hBn : 0 < binT p i PP := by
    unfold binT
    exact_mod_cast Nat.choose_pos (by omega)
  exact core (Comp Y.d.Xo₂ Y.d.c₂) (lenT p i PP) (dimFlag (dat p i)) B cs X cc (zed p i PP u1) (rhoB (dat p i) u1) R
    (binT p i PP) δ' (unitE p) C1 C2 _ (fun Z => Y.ht u1 Z) sl (fun Z => Y.dg u1 Z) (fun Z => Y.rkC (uM p i) Z)
    (fun Z => Y.degC (uM p i) Z) (Nat.cast_nonneg _) (by exact_mod_cast hTD) hB hcs hX hcc hz0 hz1 hρ0 hρ1 hR hBn hδ
    (hb1.trans hbE) h1 (hsh u1 hu) h3 h4 h5 h6 h7 h8 h9 h10 hsum

end GlobalTheory.CovTop.FromComp

end
end
