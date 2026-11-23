module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle111
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechRepresentativeChernClassTangentValue
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFockVectorHeisenbergAverageIsotropicEqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle050

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompLevelStab

theorem mem_iff_of_inv {X : Scheme.{0}} (Z : Set X) (hZ : IsClopen Z) (hI : IsIrreducible Z) (f g : X ⟶ X)
    (hfg : f ≫ g = 𝟙 X) (x : X) (hx : x ∈ Z) (hfx : f.base x ∈ Z) (y : X) : f.base y ∈ Z ↔ y ∈ Z := by
  have hgf : ∀ z, g.base (f.base z) = z := fun z => by
    have := congrArg (fun h : X ⟶ X => h.base z) hfg
    simpa using this
  have A : f.base '' Z ⊆ Z :=
    (hI.image _ f.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ ⟨_, ⟨x, hx, rfl⟩, hfx⟩
  have B : g.base '' Z ⊆ Z :=
    (hI.image _ g.continuous.continuousOn).isPreirreducible.isPreconnected.subset_isClopen hZ
      ⟨_, ⟨f.base x, hfx, rfl⟩, by rw [hgf]; exact hx⟩
  exact ⟨fun h => hgf y ▸ B ⟨_, h, rfl⟩, fun h => A ⟨y, h, rfl⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

section Moves

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l)

def mv (γ : LevelAut Dw l) : Xo.X ⟶ Xo.X := (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose

theorem mv_spec (γ : LevelAut Dw l) : ∃ ν : SABMap Xo.univ.t Xo.univ.t (mv hpq hA Xo γ),
    IsIso (mv hpq hA Xo γ) ∧ IsLevMove (mv hpq hA Xo γ) ν (liftLa γ) LinearMap.id :=
  (GlobalTheory.LevelActionLaws.exists_move hpq hA Xo γ).choose_spec

theorem x_move (c : Coeff l) (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    (move Xo c γ y).x = y.x ≫ mv hpq hA Xo γ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact (GlobalTheory.LevelActionLaws.frMove_transfer hpq hA Xo c γ i h (GlobalTheory.LevDesc.levR_move hpq hA γ y)).1

theorem mv_over (γ : LevelAut Dw l) : mv hpq hA Xo γ ≫ Xo.s = Xo.s := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  exact h.1

theorem mv_mul (c : Coeff l) (γ δ : LevelAut Dw l) : mv hpq hA Xo (γ * δ) = mv hpq hA Xo γ ≫ mv hpq hA Xo δ := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo γ
  obtain ⟨ν', i', h'⟩ := mv_spec hpq hA Xo δ
  obtain ⟨ν₂, i₂, h₂⟩ := mv_spec hpq hA Xo (γ * δ)
  obtain ⟨μ, hμ, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).2.1 _ _ ν ν'
  have hc : IsLevMove (mv hpq hA Xo γ ≫ mv hpq hA Xo δ) μ (liftLa (γ * δ)) LinearMap.id := by
    refine ⟨?_, fun a => ?_, fun a => ?_⟩
    · rw [Category.assoc, h'.1, h.1]
    · rw [GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_mul_sub γ δ a), hμ, ← Category.assoc, h.2.1,
        Category.assoc, h'.2.1, Category.assoc]
    · have e : (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a = (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) ((LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La) a) := rfl
      rw [e, hμ, ← Category.assoc, h.2.2, Category.assoc, h'.2.2, Category.assoc]
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c (γ * δ) i₂ inferInstance h₂ hc).1

theorem mv_one (c : Coeff l) : mv hpq hA Xo 1 = 𝟙 Xo.X := by
  obtain ⟨ν, i, h⟩ := mv_spec hpq hA Xo 1
  obtain ⟨ι, hι, -⟩ := (GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c).1
  have hc : IsLevMove (𝟙 Xo.X) ι (liftLa (1 : LevelAut Dw l)) LinearMap.id := by
    refine ⟨Category.id_comp _, fun a => ?_, fun a => ?_⟩
    · rw [hι, Category.comp_id, Category.id_comp]
      exact congrArg _ (GlobalTheory.LevelActionLaws.eta_congr Xo (GlobalTheory.LevelActionLaws.liftLa_one_sub a))
    · rw [hι, Category.comp_id, Category.id_comp]
      rfl
  exact (GlobalTheory.LevelActionLaws.move_unique hpq hA Xo c 1 i inferInstance h hc).1

end Moves

section Base

variable (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Xo : Moduli Dw l) (c : Coeff l)

def mvF (γ : LevelAut Dw l) : Xo.XF c ⟶ Xo.XF c :=
  pullback.lift (pullback.fst _ _ ≫ mv hpq hA Xo γ) (pullback.snd _ _) (by
    rw [Category.assoc, mv_over, pullback.condition])

theorem mvF_fst (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mv hpq hA Xo γ :=
  pullback.lift_fst _ _ _

theorem mvF_snd (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem mvF_mul (γ δ : LevelAut Dw l) : mvF hpq hA Xo c (γ * δ) = mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c δ := by
  apply pullback.hom_ext
  · rw [mvF_fst, Category.assoc, mvF_fst, ← Category.assoc, mvF_fst, Category.assoc, mv_mul hpq hA Xo c]
  · rw [mvF_snd, Category.assoc, mvF_snd, mvF_snd]

theorem mvF_one : mvF hpq hA Xo c 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mvF_fst, mv_one hpq hA Xo c, Category.comp_id, Category.id_comp]
  · rw [mvF_snd, Category.id_comp]

theorem mvF_inv_comp (γ : LevelAut Dw l) : mvF hpq hA Xo c γ⁻¹ ≫ mvF hpq hA Xo c γ = 𝟙 _ := by
  rw [← mvF_mul, inv_mul_cancel, mvF_one]

theorem mvF_comp_inv (γ : LevelAut Dw l) : mvF hpq hA Xo c γ ≫ mvF hpq hA Xo c γ⁻¹ = 𝟙 _ := by
  rw [← mvF_mul, mul_inv_cancel, mvF_one]

theorem ptF_move (γ : LevelAut Dw l) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    ptF (move Xo c γ y) = ptF y ≫ mvF hpq hA Xo c γ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mvF_fst, ← Category.assoc]
    simp only [ptF, pullback.lift_fst]
    exact x_move hpq hA Xo c γ y
  · rw [Category.assoc, mvF_snd]
    simp only [ptF, pullback.lift_snd]

variable (Z : Comp Xo c)

def stab : Subgroup (LevelAut Dw l) where
  carrier := {h | ∀ x, (mvF hpq hA Xo c h⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))}
  one_mem' := fun x => by rw [inv_one, mvF_one]; rfl
  mul_mem' := by
    intro a b ha hb x
    rw [Set.mem_setOf_eq] at ha hb
    rw [mul_inv_rev, mvF_mul, Scheme.Hom.comp_apply, ha, hb]
  inv_mem' := by
    intro a ha x
    rw [Set.mem_setOf_eq] at ha
    have e : (mvF hpq hA Xo c a⁻¹).base ((mvF hpq hA Xo c a).base x) = x := by
      have := congrArg (fun f : Xo.XF c ⟶ Xo.XF c => f.base x) (mvF_comp_inv hpq hA Xo c a)
      simpa using this
    rw [inv_inv, ← ha, e]

end Base

section Restrict

variable {hpq : 1 ≤ Dw.p + Dw.q} {hA : l.A.Coprime l.M} {Xo : Moduli Dw l} {c : Coeff l}
  (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c)

theorem mem_V₀ (x : Xo.XF c) : x ∈ Y.j ⁻¹ᵁ barComp Y Z ↔ x ∈ (Z : Set (Xo.XF c)) := j_mem_barComp Z x

theorem le_V₀ (g : LevelAut Dw l) (hg : ∀ x, (mvF hpq hA Xo c g).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c))) :
    Y.j ⁻¹ᵁ barComp Y Z ≤ mvF hpq hA Xo c g ⁻¹ᵁ (Y.j ⁻¹ᵁ barComp Y Z) := fun x hx =>
  (mem_V₀ Y Z _).2 ((hg x).2 ((mem_V₀ Y Z x).1 hx))

theorem inv_mem_stab {h : LevelAut Dw l} (hh : h ∈ stab hpq hA Xo c Z) :
    ∀ x, (mvF hpq hA Xo c h).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) := by
  have h2 := (stab hpq hA Xo c Z).inv_mem hh
  change ∀ x, (mvF hpq hA Xo c h⁻¹⁻¹).base x ∈ (Z : Set (Xo.XF c)) ↔ x ∈ (Z : Set (Xo.XF c)) at h2
  simpa only [inv_inv] using h2

def resAut (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) : Aut (V₀ Y Z) where
  asIso :=
    { hom := (mvF hpq hA Xo c h⁻¹).resLE _ _ (le_V₀ Y Z h⁻¹ hh)
      inv := (mvF hpq hA Xo c h).resLE _ _ (le_V₀ Y Z h (inv_mem_stab Z hh))
      hom_inv_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_inv_comp, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (Y.j ⁻¹ᵁ barComp Y Z).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
          Scheme.Hom.resLE_comp_ι, Category.assoc, mvF_comp_inv, Category.comp_id, Category.id_comp] }

theorem resAut_ι (h : LevelAut Dw l) (hh : h ∈ stab hpq hA Xo c Z) :
    (resAut Y Z h hh).asIso.hom ≫ i₀ Y Z = i₀ Y Z ≫ mvF hpq hA Xo c h⁻¹ :=
  Scheme.Hom.resLE_comp_ι _ _

def resHom (S : Subgroup (LevelAut Dw l)) : ↥(S ⊓ stab hpq hA Xo c Z) →* Aut (V₀ Y Z) :=
  MonoidHom.mk' (fun g => resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2) fun a b => by
    apply Aut.ext
    apply Iso.ext
    change (resAut Y Z (a * b).1 (Subgroup.mem_inf.1 (a * b).2).2).asIso.hom =
      (resAut Y Z b.1 (Subgroup.mem_inf.1 b.2).2).asIso.hom ≫
        (resAut Y Z a.1 (Subgroup.mem_inf.1 a.2).2).asIso.hom
    rw [← cancel_mono (i₀ Y Z), Category.assoc, resAut_ι, resAut_ι,
      ← Category.assoc, resAut_ι, Category.assoc, ← mvF_mul, Subgroup.coe_mul, mul_inv_rev]

theorem j₀_s₀ : j₀ Y Z ≫ s₀ Y Z = i₀ Y Z ≫ pullback.snd _ _ ≫ spMap (RingHom.id c.F) := by
  show j₀ Y Z ≫ (barComp Y Z).ι ≫ Y.s = _
  rw [← Category.assoc, j₀_ι, Category.assoc, Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ,
    Y.jQ_over]

end Restrict

theorem stab_acts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ S : Subgroup (LevelAut Dw l), ∃ (Γ : Subgroup (LevelAut Dw l)) (ρ : Γ →* Aut (V₀ Y Z)), Γ ≤ S ∧ ActsBy Γ.subtype ρ ∧ ∀ h ∈ S, ∀ y : FrPt Xo c ℂ, LiesOn Z y → LiesOn Z (move Xo c h⁻¹ y) → h ∈ Γ := by
  intro E _ _ _ H Dw l Xo c Y Z hpq hl S
  have hA : l.A.Coprime l.M := by rw [hl]; exact Nat.coprime_one_left _
  refine ⟨S ⊓ stab hpq hA Xo c Z, resHom (hpq := hpq) (hA := hA) Y Z S, inf_le_left, ⟨fun g => ?_, ?_⟩, ?_⟩
  · show (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ j₀ Y Z ≫ s₀ Y Z = j₀ Y Z ≫ s₀ Y Z
    rw [j₀_s₀, ← Category.assoc, resAut_ι, Category.assoc, ← Category.assoc (mvF _ _ _ _ _), mvF_snd]
  · intro g R _ _ y v hv
    show v ≫ (resAut Y Z g.1 (Subgroup.mem_inf.1 g.2).2).asIso.hom ≫ i₀ Y Z = _
    rw [resAut_ι, ← Category.assoc, hv, ← ptF_move]
    rfl
  · intro h hS y hy hy'
    refine Subgroup.mem_inf.2 ⟨hS, ?_⟩
    let pt : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h1 := hy' pt
    rw [ptF_move hpq hA Xo c, Scheme.Hom.comp_apply] at h1
    exact mem_iff_of_inv _ (TrivOrderTieCompare.isClopen_comp Z) Z.2.1 (mvF hpq hA Xo c h⁻¹) (mvF hpq hA Xo c h)
      (mvF_inv_comp hpq hA Xo c h) _ (hy pt) h1

end GlobalTheory.CompLevelStab
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

noncomputable section

namespace GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters Formalism.L2.Pj

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_plOver (j : Fin 2) : Nonempty (PlOver D.host j) := by
  have hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have : ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
    have hd : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
    have hg := (D.host.g_prime j).two_le
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have : 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F := Nat.pow_le_pow_left hg _
    have : 2 ≤ 2 ^ Module.finrank ℚ D.host.F := Nat.le_self_pow hd.ne' 2
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩
  rw [e, Ideal.mem_bot] at hg
  exact (D.host.g_prime j).ne_zero (by exact_mod_cast hg)

theorem isNilpotent_sub_one_of_unitri {r : ℕ} {k : Type} [Field k] {u : GL (Fin r) k} (hu : u ∈ unitri r k) :
    IsNilpotent ((u : Matrix (Fin r) (Fin r) k) - 1) := by
  have ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id := hu.1.sub Matrix.blockTriangular_one
  have hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular _ ht]
    simp [hu.2]
  refine ⟨r, ?_⟩
  have := Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)
  rwa [hc, map_pow, Polynomial.aeval_X] at this

theorem neat_typePrime (hM : D.host.g 0 * D.host.g 1 ∣ l.M) (hg : ∀ k, Dw.p + Dw.q + 1 < D.host.g k)
    (v : Sq D.host) : NeatPrime (typePrime l v) (D.host.g v.1) (Dw.p + Dw.q) ∧ (typePrime l v).IsPrime := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd (D := D) v.1).trans hM
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  refine ⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v),
    fun hmem => ?_, hg v.1⟩, hP⟩
  have h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime v.1).ne_zero
  have hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2
  have hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
    exact hmem
  exact hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))

theorem unipAt_of_unitri (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host)
    (hγ : typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1))) : UnipAt (typePrime l v) γ := by
  obtain ⟨n, hn⟩ := isNilpotent_sub_one_of_unitri hγ
  set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) :=
    ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1
    with hNm
  let π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v) := Submodule.mkQ _
  have key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      generalize ((liftLa γ - 1) ^ m) x = y
      have h1 : π (liftLa γ y) = qProj (J := typePrime l v) le_sup_left
          (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by
        rw [← liftLa_spec]; rfl
      have h2 : π y = qProj (J := typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec,
        Matrix.one_mulVec, typeRed_mulVec]
  refine ⟨n, fun x => ?_⟩
  have h := key n x
  rw [hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem exists_index (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)) (hS : S = grpHR fr ∨ ∃ k, S = grpGHR fr k) :
    ∃ j : Fin 2, ∀ γ ∈ S, ∀ v : Sq D.host, v.1 = j → typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1)) := by
  rcases hS with rfl | ⟨k, rfl⟩
  · exact ⟨0, fun γ hγ v _ => hγ v trivial⟩
  · refine ⟨k + 1, fun γ hγ v hv => hγ v ?_⟩
    show v.1 ≠ k
    rw [hv]; fin_cases k <;> decide

end GlobalTheory.OrbitSep.UnipPrime


open GlobalTheory.OrbitSep.UnipPrime GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters in
theorem GlobalTheory.OrbitSep.exists_neatPrime_unipAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  intro D H Dw l hM hg fr S hS
  obtain ⟨j, hj⟩ := exists_index fr S hS
  obtain ⟨w⟩ := exists_plOver (D := D) j
  let v : Sq D.host := ⟨j, w⟩
  obtain ⟨hN, -⟩ := neat_typePrime (Dw := Dw) hM hg v
  exact ⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.hecke_bundle_trivial_geometric_fibre : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  first | (exact @GlobalTheory.HeckeFibre.fibre_triv) | (exact GlobalTheory.HeckeFibre.fibre_triv) | (intros; apply GlobalTheory.HeckeFibre.fibre_triv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isCechRepresentative_chernClass_tangentValue : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (I : Type) [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) → ∀ v : epsR K ⟶ A, IsTangent v → ∀ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), (∀ j, (V j).1 ≤ L.U (τ j)) → IsRep (fun j => (V j).1) (∑ k, tanVal v (ω k) • c k) (fun j j' => dlog L v (τ j) (τ j')) := by
  first | exact @GlobalTheory.CechKS.isRep_chern_tanVal | exact GlobalTheory.CechKS.isRep_chern_tanVal | (intros; apply GlobalTheory.CechKS.isRep_chern_tanVal <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_prod_localComponents_eq_primePart : ∀ {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (hG : V.gram = 1) (q : ℕ), q.Prime → ∀ g : Formalism.L2.Theta.GA D V, ∃ l : List (Formalism.L2.Theta.GA D V), (∀ h ∈ l, ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F), Formalism.L2.Theta.IsPlaceIdem D v ε ∧ (q : 𝓞 D.host.F) ∈ v.asIdeal ∧ GlobalTheory.WeilParts.SuppPl ε V h) ∧ GlobalTheory.BotClassDict.finStd V hG l.prod = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) (GlobalTheory.BotClassDict.finStd V hG g) := by
  first | exact @GlobalTheory.PrimePart.exists_prod_eq_part | exact GlobalTheory.PrimePart.exists_prod_eq_part | (intros; apply GlobalTheory.PrimePart.exists_prod_eq_part <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

namespace GlobalTheory.BigOn.PageNumbers

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem le_sup_fin (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (k : ℕ) (hk : k < D.R.m) :
    WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK (k + 1)) ≤
      Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)) := by
  have h := Finset.le_sup (f := fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1)))
    (Finset.mem_univ (⟨k, hk⟩ : Fin D.R.m))
  exact h

theorem sup_fin_eq_topDeg (Tp : ParamsT D L Pm) (hK : DV.KapDef D) :
    (Finset.univ.sup fun j : Fin D.R.m => WeightAlgebra.DF (Formalism.MainNotions.DIV.Cons.lR Tp hK ((j : ℕ) + 1))) = GlobalTheory.IndexAssembly.topDeg Tp hK := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => GlobalTheory.IndexAssembly.le_topDeg Tp hK ⟨by omega, by omega⟩
  · refine Finset.sup_le fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact le_sup_fin Tp hK k (by omega)

end GlobalTheory.BigOn.PageNumbers

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.BigOn

end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

theorem _root_.GlobalTheory.T.levelFockVector_heisenbergAverage_isotropic_eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ Q h g ξ, IsoVec (Wc D i) ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin (Vc D i).rank → AE D, ∑ k, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ (a k)) (om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f Q)) = 0 := by
  first | exact @GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level | exact GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level | (intros; apply GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineForm_tangentValue_mul_abelianScheme : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (f : Form (A.hom ≫ 𝟙 (Sp R))) (a b : epsR R ⟶ A), tanVal (a * b) f = tanVal a f + tanVal b f := by
  first | exact @GlobalTheory.TanAdd.tanVal_mul_all | exact GlobalTheory.TanAdd.tanVal_mul_all | (intros; apply GlobalTheory.TanAdd.tanVal_mul_all <;> assumption)
end
