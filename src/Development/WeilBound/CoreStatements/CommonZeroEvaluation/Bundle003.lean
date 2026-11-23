module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjEmbRtOfNe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead

@[expose] public section

section

open scoped Matrix

namespace ModelDimension

theorem generic_flag_transition_matrices : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  intro K L _ _ _ E₀ F _ _ _ _ j S _ r V b d hg e he hli
  have hj : ∀ (a : K) x, j (a • x) = algebraMap K L a • j x := by
    obtain ⟨_, _, -, h, -⟩ := hg
    exact h
  have hli₀ : ∀ s, LinearIndependent K (e s) := fun s => by
    refine Fintype.linearIndependent_iff.2 fun g hg0 k => ?_
    have h1 : ∑ l, algebraMap K L (g l) • j (e s l) = 0 := by
      have := congrArg j hg0

      rw [map_sum, map_zero] at this
      simpa only [hj] using this
    have h2 := Fintype.linearIndependent_iff.1 (hli s) _ h1 k
    exact (map_eq_zero_iff _ (algebraMap K L).injective).1 h2
  obtain ⟨v, Tm, h1, h0, hi, hd, hb, hT0, hTd⟩ := GlobalTheory.CompanionTheory.Ar.Rec.ReadEx.lin_core j V b d hg e hli₀ he hli
  refine ⟨v, Tm, h1, h0, hi, ?_, hb, hT0, hTd⟩
  rw [← GlobalTheory.CompanionTheory.Ar.Rec.ReadEx.adjoin_all_eq_strict v h1 h0]
  exact hd

end ModelDimension
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace ModelDimension

theorem generic_frame_constant_algebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), letI := Small.cstAlg Or; ∀ (y' : FrPt Xo c RM.Ω), Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f → ∀ (Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li) (Tm : ∀ s, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω), (∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k)) → (∀ s i, Or.Fl.b s i = ∑ m, Tm s i m • Wv s m) → (∀ s i m, i < m → Tm s i m = 0) → (∀ s i, Tm s i i ≠ 0) → ∃ t : Ix Dw → (RM.Ω)ˣ, FrBor t y' Fr.y₀ := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Fr
  letI := Small.cstAlg Or
  intro y' hy Wv Tm hW hb hT0 hTd
  have hpF : Small.ptF y' = Small.ptF Fr.y₀ := Small.ptF_eq_of_ptY_eq Y (hy.trans Fr.pt_eq.symm)
  have hx : y'.x = Fr.y₀.x := by
    rw [← Small.ptF_fst y', hpF, Small.ptF_fst]
  obtain ⟨M₁, e₁⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Or.𝔐.m.cart RM.Ω Or.𝔐.ξ Or.𝔐.Li).2 Or.𝔐.M
  obtain ⟨N, hN, -⟩ := ReadEx.exists_univ_model Y (Small.ptF Fr.y₀) Fr.pt_eq M₁ (Small.ptF_fst Fr.y₀)
  refine ReadEx.frBor_of_comb y' Fr.y₀ hx.symm fun τ i => ?_
  obtain ⟨s, rfl⟩ := (Small.labelC_bijective H).2 τ
  have h1 : y'.u (Small.labelC s) = fun m => (N.pt (Wv s (Fin.cast (Small.mult_labelC Dw s) m))).left :=
    funext fun m => ((ReadEx.pt_eq_u_iff Y y' hpF hN _ m _).2
      ((hW s (Fin.cast (Small.mult_labelC Dw s) m)).symm.trans (e₁ _))).symm
  have h2 : (N.pt (Or.Fl.b s (Fin.cast (Small.mult_labelC Dw s) i))).left = Fr.y₀.u (Small.labelC s) i :=
    (ReadEx.pt_eq_u_iff Y Fr.y₀ rfl hN _ i _).2 ((Fr.tan_eq s (Fin.cast (Small.mult_labelC Dw s) i)).trans (e₁ _))
  refine ⟨fun m => Tm s (Fin.cast (Small.mult_labelC Dw s) i) (Fin.cast (Small.mult_labelC Dw s) m),
    isUnit_iff_ne_zero.2 (hTd s _), fun j hij => hT0 s _ _ hij, ?_⟩
  rw [hx, h1, ReadEx.comb_iff N, ← h2, hb]
  have hs := Equiv.sum_comp (finCongr (Small.mult_labelC Dw s))
    (fun m => Tm s (Fin.cast (Small.mult_labelC Dw s) i) m • Wv s m)
  exact congrArg (fun e => (N.pt e).left) hs.symm

end ModelDimension
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

namespace ModelDimension

theorem component_kappa_equivalence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c) (ψ : kap Z ≃+* Or.𝔐.Ω₀), spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ → ∀ (y₀ : FrPt Xo c (kap Z)), y₀.x = xGen Z → letI := Small.cstAlg Or; ∀ (χ : kap Z →ₐ[c.F] RM.Ω) (y₂ : FrPt Xo c RM.Ω), χ.toRingHom = Or.𝔐.fn.comp ψ.toRingHom → FrMap χ y₀ y₂ → Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f ∧ ∀ s, ∃ e : Fin (labelRk Dw s) → Or.Fl.Li₀, (∀ k, e k ∈ Or.Fl.V₀ s) ∧ (LinearIndependent RM.Ω fun k => Or.Fl.j (e k)) ∧ ∀ k, (Or.𝔐.M.pt (Or.Fl.j (e k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k) := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Z ψ hψ y₀ hy₀
  letI algΩ := Small.cstAlg Or
  intro χ y₂ hχ hFr
  have hc : ∀ a : c.F, Or.𝔐.fn (ψ (algebraMap c.F (kap Z) a)) = Or.𝔐.cst a := fun a =>
    (RingHom.congr_fun hχ _).symm.trans (χ.commutes a)
  have hp0 : Small.ptF y₀ = genSp Z := by
    apply pullback.hom_ext
    · rw [Small.ptF_fst, hy₀]; rfl
    · rw [Small.ptF_snd]; exact Spec.map_preimage _
  have hpt : Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f := by
    have hfn : Or.𝔐.ξ ≫ Or.𝔐.f = spMap Or.𝔐.fn ≫ Or.𝔐.ξ₀ := Or.𝔐.fn_over
    rw [Small.ptY_map Y hFr, hfn, ← hψ, hχ, ← ReadEx.spc, Small.ptY, hp0, Category.assoc]
  refine ⟨hpt, fun s => ?_⟩
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.exists_genFrame Or
  have hpF : Small.ptF y₂ = Small.ptF Fr.y₀ := Small.ptF_eq_of_ptY_eq Y (hpt.trans Fr.pt_eq.symm)
  letI alg₀ : Algebra c.F Or.𝔐.Ω₀ := ((ψ.toRingHom).comp (algebraMap c.F (kap Z))).toAlgebra
  let ψA : kap Z →ₐ[c.F] Or.𝔐.Ω₀ := { ψ.toRingHom with commutes' := fun _ => rfl }
  obtain ⟨y₁, h₁⟩ := GlobalTheory.FrameNorm.exists_frMap_along ψA y₀
  have hz₀ : Small.ptF y₁ ≫ Y.j = Or.𝔐.ξ₀ := by
    rw [Small.ptF_map h₁, hp0, Category.assoc]; exact hψ
  have hx₂ : y₂.x = Fr.y₀.x := by
    rw [← Small.ptF_fst y₂, hpF, Small.ptF_fst]
  obtain ⟨M₁, e₁⟩ := (GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback _ _ _ _ _ _ Or.𝔐.m.cart RM.Ω Or.𝔐.ξ Or.𝔐.Li).2 Or.𝔐.M
  obtain ⟨N, hN, hNa⟩ := ReadEx.exists_univ_model Y (Small.ptF Fr.y₀) Fr.pt_eq M₁ (Small.ptF_fst Fr.y₀)
  obtain ⟨N₀, hN₀, -⟩ := ReadEx.exists_univ_model Y (Small.ptF y₁) hz₀ Or.Fl.M₀ (Small.ptF_fst y₁)
  have hex : ∀ τ k, ∃ e, (N₀.pt e).left = y₁.u τ k := fun τ k => ReadEx.exists_pt N₀ (y₁.tan τ k)
  choose ec hec using hex
  have hM₀ : ∀ τ k, Small.tanY Y y₁ τ k = (Or.Fl.M₀.pt (ec τ k)).left := fun τ k =>
    (ReadEx.pt_eq_u_iff Y y₁ rfl hN₀ τ k _).1 (hec τ k)
  have hcomp : spMap (GlobalTheory.CompanionTheory.Ar.dualMap χ.toRingHom) =
      spMap (GlobalTheory.CompanionTheory.Ar.dualMap Or.𝔐.fn) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap ψA.toRingHom) := by
    rw [ReadEx.spc, hχ]
    exact congrArg spMap (ReadEx.dualMap_comp₂ ψ.toRingHom Or.𝔐.fn)
  have ht : ∀ τ k, (Or.𝔐.M.pt (Or.Fl.j (ec τ k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ τ k := fun τ k => by
    rw [Or.Fl.j_pt, ← hM₀, Small.tanY_map Y h₁, Small.tanY_map Y hFr, hcomp, Category.assoc]
  have hy₂ : ∀ τ k, (N.pt (Or.Fl.j (ec τ k))).left = y₂.u τ k := fun τ k =>
    (ReadEx.pt_eq_u_iff Y y₂ hpF hN τ k _).2 ((ht τ k).symm.trans (e₁ _))
  refine ⟨fun k => ec (Small.labelC s) (Small.labelFin Dw s k), fun k => ?_,
    (ReadEx.indep_of_basis y₂ hx₂ N _ _ (hy₂ (Small.labelC s))).comp (Small.labelFin Dw s) (Fin.cast_injective (Small.mult_labelC Dw s).symm),
    fun k => ht _ _⟩
  refine (Or.Fl.V₀_mem s _).2 ?_
  have hρ : ∀ (a : 𝓞 E) (e : Or.𝔐.Li), (M₁.pt (Or.𝔐.ρ a e)).left = (M₁.pt e).left ≫ (Y.t.act.act a).left := fun a e => by
    rw [← e₁, ← e₁, Or.𝔐.act a e, CategoryTheory.Over.comp_left, Category.assoc, Or.𝔐.m.act, Category.assoc]
  have hact := hNa (fun a e => Or.𝔐.ρ a e) hρ
  show _ ∈ eigSp Or.𝔐.ρ (Or.𝔐.emb s)
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro a
  apply N.inj
  apply CategoryTheory.Over.OverMorphism.ext
  have h3 := y₂.eig (Small.labelC s) (Small.labelFin Dw s k) a
  rw [hact a, hy₂, h3, LinearMap.smul_apply, LinearMap.id_apply, N.smul, hy₂, Small.embK_labelC]
  rfl

end ModelDimension
end
