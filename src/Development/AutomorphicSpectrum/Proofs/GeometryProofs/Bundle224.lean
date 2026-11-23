module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompare
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle075
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRing
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionFieldExtensionExists
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
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
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.KerBd

variable {k : Type} [Field k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Wd (B : Germ.FB k d O) (a : O) : Submodule k (Fin d → k) where
  carrier := {u | (rho B a).mulVec u = 0 ∧ ∀ z : Fin d → k, (rho B (star a)).mulVec z = 0 →
      z ⬝ᵥ (bil (B.ad a) 1 1).transpose.mulVec u = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by simp [Matrix.mulVec_add, hu1, hv1], fun z hz => ?_⟩
    simp [Matrix.mulVec_add, dotProduct_add, hu2 z hz, hv2 z hz]
  zero_mem' := ⟨by simp, fun z _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    refine ⟨by simp [Matrix.mulVec_smul, hu1], fun z hz => ?_⟩
    simp [Matrix.mulVec_smul, dotProduct_smul, hu2 z hz]

theorem Wd_le (B : Germ.FB k d O) (a : O) : Wd B a ≤ LinearMap.ker (Matrix.toLin' (rho B a)) :=
  fun u hu => by simpa [Matrix.toLin'_apply] using hu.1

theorem finrank_ker_transpose (M : Matrix (Fin d) (Fin d) k) :
    Module.finrank k (LinearMap.ker (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M.transpose)
  have h3 : Module.finrank k (LinearMap.range (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.range (Matrix.toLin' M)) := by
    exact (Matrix.finrank_range_mulVecLin M.transpose).trans ((Matrix.rank_transpose M).trans (Matrix.finrank_range_mulVecLin M).symm)
  omega

theorem finrank_ker_rhoH_le (B : Germ.FB k d O) (a : O) :
    Module.finrank k (LinearMap.ker (rhoH B a)) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)))) + Module.finrank k (Wd B a) := by
  set K := LinearMap.ker (rhoH B a)
  let f : K →ₗ[k] (Fin d → k) := (LinearMap.fst k (Fin d → k) (Fin d → k)).comp K.subtype
  have hrange : LinearMap.range f ≤ Wd B a := by
    rintro _ ⟨y, rfl⟩
    have hy : rhoH B a y = 0 := y.2
    rw [rhoH_apply, Prod.mk_eq_zero] at hy
    refine ⟨hy.1, fun z hz => ?_⟩
    have h2 : (bil (B.ad a) 1 1).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).1 =
        (rho B (star a)).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).2 := (sub_eq_zero.1 hy.2).symm
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.fst_apply]
    rw [h2, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz, zero_dotProduct]
  let g : LinearMap.ker f →ₗ[k] (Fin d → k) :=
    (LinearMap.snd k (Fin d → k) (Fin d → k)).comp (K.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have h2 : ((y : K) : (Fin d → k) × (Fin d → k)).2 = 0 := hy
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  have hgr : LinearMap.range g ≤ LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose) := by
    rintro _ ⟨y, rfl⟩
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have hy : rhoH B a (y : K) = 0 := (y : K).2
    rw [rhoH_apply, Prod.mk_eq_zero, h1] at hy
    simpa [g, Matrix.toLin'_apply] using hy.2
  have e1 := LinearMap.finrank_range_add_finrank_ker f
  have e2 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (Wd B a) := Submodule.finrank_mono hrange
  have e3 : Module.finrank k (LinearMap.ker f) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose)) := by
    rw [← LinearMap.finrank_range_of_inj hg]; exact Submodule.finrank_mono hgr
  rw [finrank_ker_transpose] at e3
  omega

end GlobalTheory.CompanionTheory.Ar.Flat.KerBd

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.KerBd in
theorem lemF_ker_order_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  intro E _ _ _ H _ hbar k _ _ p _ _ t hprop hK d g a A _ _ _ i hpb
  obtain ⟨A', _, _, _, _, hrk, D, T, hD, hT, hder, hprim, horth⟩ :=
    GlobalTheory.T.proper_group_germ_finite_subscheme E H hbar k p t hprop hK d g a A i hpb
  let W0 : Submodule k (LinearMap.ker (Matrix.toLin' (rho g.B a))) :=
    (Wd g.B a).comap (LinearMap.ker (Matrix.toLin' (rho g.B a))).subtype
  have hW0 : Module.finrank k W0 = Module.finrank k (Wd g.B a) :=
    (Submodule.comapSubtypeEquivOfLe (Wd_le g.B a)).finrank_eq
  have hc := GlobalTheory.T.primitive_derivation_pairing k p A' (LinearMap.range T) (W0.map D)
    (by rintro _ ⟨z, rfl⟩; exact hprim z)
    (by rintro _ ⟨u, -, rfl⟩; exact hder u)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨z, rfl⟩
      have hz : (rho g.B (star a)).mulVec (z : Fin d → k) = 0 := by
        have := z.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      exact horth u z ((hu : (u : Fin d → k) ∈ Wd g.B a).2 z hz))
  rw [LinearMap.finrank_range_of_inj hT, ← (Submodule.equivMapOfInjective D hD W0).finrank_eq, hW0, hrk] at hc
  exact (pow_dvd_pow p (finrank_ker_rhoH_le g.B a)).trans hc

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Comps

theorem finite_maximal_points (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] [T0Space X] : {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Finite := by
  refine Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  · intro x hx
    have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
    have hg := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hg
    have hs : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact mem_irreducibleComponent
    have he := hx _ hs
    show closure {x} ∈ irreducibleComponents X
    rw [← he, hg.def]
    exact hZ
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.2 h).eq

theorem nonempty_maximal_points (X : Type) [TopologicalSpace X] [QuasiSober X] [T0Space X] [Nonempty X] :
    {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hg
  refine ⟨hirr.genericPoint, fun x' hx' => ?_⟩
  have hm : Maximal IsIrreducible (irreducibleComponent x) := hZ
  have hsub : irreducibleComponent x ⊆ closure {x'} := by
    rw [← hg.def]
    exact hx'.closure_subset
  have hirr' : IsIrreducible (closure {x'}) := isIrreducible_singleton.closure
  have heq : closure {x'} = irreducibleComponent x := (hm.eq_of_subset hirr' hsub).symm
  exact (inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq

theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}

theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

theorem finite_nonempty_maximal : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)),
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧
      {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.root_model_flag_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) [Fintype (CMType H)] (M R : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (𝔐₀ : HodgeCpt Y S₀ R.y) (Fl : 𝔐.Flag) (Fl₀ : 𝔐₀.Flag) (i : R.Ω →+* M.Ω) (e : CMType H × Fin (D.p + D.q) → M.Ω) (e₀ : CMType H × Fin (D.p + D.q) → R.Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ s k, (𝔐.M.pt (Fl.b s k)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s k)).left ≫ 𝔐₀.m.φ) → Fl.RootLines M.xdeg e → Fl₀.RootLines R.xdeg e₀ → ∀ r, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (e₀ r) / e r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join | exact GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.CloseGen.genUnit_join <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem orderAt_of_unit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {σ ϖ ϖ' : Ω}
    {M : ℕ} {a : ℤ} {p : Cpt ξ} (h : OrderAt L σ ϖ M a p) (hu : unitAt ξ p (ϖ / ϖ')) : OrderAt L σ ϖ' M a p := by
  obtain ⟨e, c, he, hL, hσ, hc⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  have h0 : ϖ ≠ 0 := fun h => hu.1 (by simp [h])
  have h1 : ϖ' ≠ 0 := fun h => hu.1 (by simp [h])
  have hz : ∀ n : ℤ, unitAt ξ p ((ϖ / ϖ') ^ n) := fun n => by
    cases n with
    | ofNat m => simpa using ZUnit.pow hu m
    | negSucc m => simpa using ZUnit.inv (ZUnit.pow hu (m + 1))
  have : c ^ M / ϖ' ^ a = c ^ M / ϖ ^ a * (ϖ / ϖ') ^ a := by
    rw [div_zpow]
    field_simp
  rw [this]
  exact ZUnit.mul hc (hz a)

theorem exists_orders (hZ : PropZ) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} [Finite κ] {x : κ → Ω} {F' : Type} [Field F'] [NumberField F'] (ψ : F' →+* Ω)
    (hcl : ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ x) (hN : NormalCpt ξ) (L : Lat ξ Ω) (σ : Ω)
    (hL : L.IsVB 1 ⊤) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L σ (ψ π) m k p := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hplace : ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) →
        OrderAt L σ (ψ π) M a p := by
    intro v π hπ
    obtain ⟨O, _, _, _, _, X', ξ', s, g, ϖ, hs, hϖ, hinj, hξs, hξg, hgen', hall', hϖπ, hrange, hreg, hsurj⟩ :=
      GlobalTheory.T.dvr_model_of_number_field_place X Ω ξ κ x F' ψ v π hall ht hN hπ
    obtain ⟨ℓ, hℓ, hℓv⟩ := GlobalTheory.T.exists_prime_dividing_uniformizer F' v π hπ
    obtain ⟨u, hu⟩ : ∃ u : O, algebraMap O Ω u = ψ ((ℓ : F') / π) :=
      (hrange _).2 ⟨_, hℓv, rfl⟩
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hcc : ConstClosed O Ω := by
      intro a ha
      obtain ⟨f, hf, hfa⟩ := ha
      have hlift : f.map (algebraMap O Ω) ∈ Polynomial.lifts ψ := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        obtain ⟨b, -, hb⟩ := (hrange _).1 ⟨f.coeff n, rfl⟩
        exact ⟨b, hb⟩
      obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts _).1 hlift
      have hne : f' ≠ 0 := by
        rintro rfl
        rw [Polynomial.map_zero] at hf'
        exact hf ((Polynomial.map_eq_zero_iff hinj).1 hf'.symm)
      obtain ⟨b, rfl⟩ := hcl a ⟨f', hne, by
        rw [← Polynomial.eval_map, hf', Polynomial.eval_map]
        exact hfa⟩
      by_cases hb : v.valuation F' b ≤ 1
      · obtain ⟨x₀, hx₀⟩ := (hrange (ψ b)).2 ⟨b, hb, rfl⟩
        exact ⟨x₀, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx₀.symm⟩
      · have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hb' : v.valuation F' b⁻¹ ≤ 1 := by
          rw [map_inv₀]
          exact inv_le_one_of_one_le₀ (le_of_not_ge hb)
        obtain ⟨y₀, hy₀⟩ := (hrange (ψ b⁻¹)).2 ⟨b⁻¹, hb', rfl⟩
        refine ⟨1, y₀, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hy₀
          exact inv_ne_zero hb0 ((map_eq_zero ψ).1 hy₀.symm)
        · rw [hy₀, ← map_mul, mul_inv_cancel₀ hb0, map_one, map_one]
    have hℓu : (ℓ : Ω) = algebraMap O Ω (ϖ * u) := by
      rw [map_mul, hϖπ, hu, ← map_mul, mul_div_cancel₀ _ hπ0, map_natCast]
    obtain ⟨M, a, hM, h⟩ := @GlobalTheory.T.proper_dvr_model_lattice_valuation X X' Ω _ _ ξ ξ' g O _ _ _ _ s hs ϖ L σ ℓ u hZ hϖ hinj hξs hξg ht.gen hgen' hall'
      hN hcc hreg hL hg hℓu (hp ℓ hℓ)
    refine ⟨M, a, hM, fun p hv => ?_⟩
    have := h p (hsurj p hv)
    rwa [hϖπ] at this
  obtain ⟨s, hs1, hs2, hs3⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ κ x hall ht
  obtain ⟨n, hn, hgn⟩ := @GlobalTheory.T.lattice_generator_invert_constant X Ω _ ξ ℤ _ _ _ s _ hs1 hs2 hs3 (Int.cast_injective) ht.gen L Set.univ 1 σ
    one_ne_zero (fun _ _ => trivial) hL hg
  have hn' : ((n : F'))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F') ((n : F'))⁻¹
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  choose M a hM hord using fun v => hplace v (π v) (hπ v)
  let T := HeightOneSpectrum.Support (𝓞 F') ((n : F'))⁻¹
  let r₀ : HeightOneSpectrum (𝓞 F') → ℚ := fun v => if v ∈ T then (a v : ℚ) / M v else 0
  have hr₀ : (Function.support r₀).Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (if_neg h)
  refine ⟨Finsupp.ofSupportFinite r₀ hr₀, fun v π' hπ' => ?_⟩
  have hrv : (Finsupp.ofSupportFinite r₀ hr₀) v = r₀ v := rfl
  rw [hrv]
  by_cases hv : v ∈ T
  · have hMv : (M v : ℚ) ≠ 0 := by exact_mod_cast (hM v).ne'
    refine ⟨M v, a v, hM v, by simp only [r₀, if_pos hv]; field_simp, fun p hp => ?_⟩
    refine orderAt_of_unit (hord v p hp) ?_
    have h0 : π' ≠ 0 := by
      rintro rfl
      simp at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have h1 : π v ≠ 0 := by
      intro h
      have := hπ v
      rw [h] at this
      simp at this
      exact WithZero.exp_ne_zero this.symm
    have e1 : v.valuation F' (π v / π') = 1 := by
      rw [map_div₀, hπ v, hπ', div_self (WithZero.exp_ne_zero)]
    have e2 : v.valuation F' (π v / π')⁻¹ = 1 := by rw [map_inv₀, e1, inv_one]
    rw [← map_div₀]
    exact ⟨(map_ne_zero ψ).2 (div_ne_zero h1 h0), hp _ e1.le, by rw [← map_inv₀]; exact hp _ e2.le⟩
  · refine ⟨1, 0, one_pos, by simp only [r₀, if_neg hv]; simp, fun p hp => ?_⟩
    have h1 : v.valuation F' (n : F') ≤ 1 := by
      have := v.valuation_le_one (K := F') (n : 𝓞 F')
      simpa using this
    have h2 : v.valuation F' ((n : F'))⁻¹ ≤ 1 := not_lt.1 hv
    have hu : unitAt ξ p (algebraMap ℤ Ω n) := by
      have e : algebraMap ℤ Ω n = ψ (n : F') := by simp
      rw [e]
      exact ⟨(map_ne_zero ψ).2 (by exact_mod_cast hn), hp _ h1, by rw [← map_inv₀]; exact hp _ h2⟩
    have := hgn p hu
    exact orderAt_one_zero.2 this

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isGeom_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty → (∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U → ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P) → Z.IsGeom := by
  exact @PositivityTheory.Xgn.geometric_of_periods

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_model_torus_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg


theorem _root_.GlobalTheory.T.torsion_point_line_bundle_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (O C : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field C] [Algebra O C] [FaithfulSMul O C] (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → ∀ (i : D.t.PP.L.ι) (h : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i)) (b : Sp C ⟶ Sp (𝓞 L)), b = spMap (algebraMap O C) ≫ spMap ρ → ∀ (yC : Over.mk b ⟶ D.t.G), yC.left = spMap (algebraMap O C) ≫ y.left → ∀ T : C, TorsVal D.t.PP s yC N T → ∃ ε : Oˣ, T = algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) * ε) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.torsVal_eq_unit_mul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem _root_.GlobalTheory.T.torsion_field_extension_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (m : ℕ) (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G), 1 ≤ m → x ^ m = 1 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (_ : Algebra L K') (_ : IsScalarTower L K K'), ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower L K' L'] (D' : PPData H L') (e : D.Ext D'), ∃ (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L'), d ≠ 0 ∧ ∀ (F : Type) [Field F] (f : L' →+* F) (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (b : Sp F ⟶ Sp (𝓞 L)) (xF yF : Over.mk b ⟶ D.t.G) (N : ℕ) (T T' : F), xF.left = spMap ((f.comp (algebraMap K' L')).comp (algebraMap K K')) ≫ x.left → yF.left = y.left ≫ e.φ → TorsVal D'.t.PP s y N T → TorsVal D.t.PP th (xF * yF ^ m) (N * m) T' → ∃ r : ℕ, 1 ≤ r ∧ (T ^ (m ^ 2)) ^ r = (f (d : L') ^ ((N * m) ^ 2) * T') ^ r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_on_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t₀ : SAB H S') (t : SAB H S) (f : S' ⟶ S) (_ : SABMap t₀ t f) (z₀ : Sp ℂ ⟶ S') (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (z₀ ≫ f) V) (core : InnerProductSpace.Core ℂ V) (W : Set V), (0 : V) ∈ W → Submodule.span ℂ W = ⊤ → (∀ a ∈ W, ∀ b ∈ W, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b)) → ∀ a b : V, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | exact GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span <;> assumption)
end
