module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.Base
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TranscendentalPeriodUnits.IsUOfIsUnit
import GroundTheory.PAdicHodge.ACrisBdRGalois
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle439
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInJAlt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.Bundle002
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison.HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem qC_eq (q : ℚ_[l]) : qC l q = algebraMap ℚ_[l] ℂ_[l] q :=
  (IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l] q).symm

theorem th_alg (x : Formalism.Per6.BdRp l) : period_ring_base.th l (algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) x) = Formalism.Per6.θD l x := by
  have h : algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) x ∈ period_ring_base.Plus l := ⟨x, rfl⟩
  rw [period_ring_base.th, dite_eq_left h]
  exact congrArg _ (IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (RingHom.mem_range.1 h).choose_spec)

theorem th_qQ (q : ℚ_[l]) : period_ring_base.th l (qQ l q) = qC l q := ((period_ring_base.base l).th_q q).2.trans (qC_eq q).symm

theorem θA_zA (z : ℤ_[l]) : θA l (zA l z) = qC l (z : ℚ_[l]) := by
  have e : ACris.iota ℂ_[l] l (zA l z) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (z : ℚ_[l]) := ACris.iota_padicInt z
  exact (congrArg (Formalism.Per6.θD l) e).trans ((th_alg _).symm.trans (th_qQ _))

theorem σC_qC (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (q : ℚ_[l]) : period_ring_base.σC g (qC l q) = qC l q := by
  rw [← th_qQ, ← (period_ring_base.base l).th_σ g _ ((period_ring_base.base l).th_q q).1, σD_qQ]

theorem χ_ne (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : period_ring_base.χ g ≠ 0 := by
  intro h0
  have h1 := σD_tQ (l := l) g
  rw [h0, map_zero, zero_mul, map_eq_zero_iff _ (Formalism.Per6.σD g).injective] at h1
  exact DeRhamTwist.Twist.tQ_ne h1

theorem sSup_pb {X X' : Scheme.{0}} (D : E.LineData X) (f : X' ⟶ X) (h : sSup (Pb.𝒱D D) = ⊤) : sSup (Pb.𝒱D (D.pb f)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx : f x ∈ sSup (Pb.𝒱D D) := h ▸ trivial
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  refine TopologicalSpace.Opens.mem_sSup.2 ⟨f ⁻¹ᵁ V, ⟨pullback.lift ((f ∣_ V) ≫ σ) (f ⁻¹ᵁ V).ι ?_, ?_⟩, hV⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact pullback.lift_snd _ _ _

theorem proper_q {M : Model l K} (h : M.Sm) : IsProper M.q := by
  have := AdicGeo.proper_p h.1
  infer_instance

theorem smooth_q {M : Model l K} (h : M.Sm) : Smooth M.q := by
  have := h.2
  infer_instance

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT

open PAlg

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

theorem sub_mulTo (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F') (h) (c : R) (hc) (c' a : R') (hc') (e : σ c = a * c')
    (j : ℕ) (y : CH.H F j) :
    (subMor m S S' h).pull j ((mulTo c S hc).pull j y) = a • (mulTo c' S' hc').pull j (m.pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • z.1 (s ⋙ m.G)) = a • c' • m.τ _ (z.1 (s ⋙ m.G))
  rw [LinearMap.map_smulₛₗ, e, mul_smul]

theorem sub_mulSub (m : CH.Mor F F' σ) (S₁ S₂ : CH.SubF F) (S₁' S₂' : CH.SubF F') (h₁ h₂) (c : R) (hc) (c' : R') (hc') (e : σ c = c')
    (j : ℕ) (y : CH.H S₁.fn j) :
    (subMor m S₂ S₂' h₂).pull j ((mulSub c S₁ S₂ hc).pull j y) = (mulSub c' S₁' S₂' hc').pull j ((subMor m S₁ S₁' h₁).pull j y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change m.τ _ (c • (show S₁.S _ from z.1 (s ⋙ m.G)).1) = c' • m.τ _ (show S₁.S _ from z.1 (s ⋙ m.G)).1
  rw [LinearMap.map_smulₛₗ, e]

theorem mulSub_mulTo (S S' : CH.SubF F) (c c' c'' : R) (h h' h'') (e : c' * c = c'') (j : ℕ) (y : CH.H F j) :
    (mulSub c' S S' h').pull j ((mulTo c S h).pull j y) = (mulTo c'' S' h'').pull j y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  change c' • c • z.1 s = c'' • z.1 s
  rw [smul_smul, e]

theorem sub_square {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{0} R} {F₂ : C₂ ⥤ ModuleCat.{0} R} {F₃ : C₃ ⥤ ModuleCat.{0} R} {F₄ : C₄ ⥤ ModuleCat.{0} R}
    {σ₁ σ₂ σ₃ σ₄ : R →+* R} (τ : R →+* R) [RingHomCompTriple σ₁ σ₂ τ] [RingHomCompTriple σ₃ σ₄ τ]
    (m : CH.Mor F₁ F₂ σ₁) (b : CH.Mor F₂ F₃ σ₂) (b' : CH.Mor F₁ F₄ σ₃) (q : CH.Mor F₄ F₃ σ₄)
    (S₁ : CH.SubF F₁) (S₂ : CH.SubF F₂) (S₃ : CH.SubF F₃) (S₄ : CH.SubF F₄) (hm hb hb' hq)
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x)) (n : ℕ) (x : CH.H S₁.fn n) :
    (subMor b S₂ S₃ hb).pull n ((subMor m S₁ S₂ hm).pull n x) = (subMor q S₄ S₃ hq).pull n ((subMor b' S₁ S₄ hb').pull n x) := by
  rw [pull_pull τ, pull_pull τ]
  exact CrystallineSemistableComparison.P.prism ((subMor m S₁ S₂ hm).comp (σ'' := τ) (subMor b S₂ S₃ hb))
    ((subMor b' S₁ S₄ hb').comp (σ'' := τ) (subMor q S₄ S₃ hq)) η (fun T x => Subtype.ext (hτ T x.1)) n x

end Gen

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section P
variable (ht : TFil l) (P : PAlg l ⥤ Type)

def shT {r r' : ℕ} (k : ℕ) (h : r + k = r') (n : ℕ) : CH.Mor (TT P r n).fn (TT P r' n).fn (RingHom.id _) :=
  mulSub (tA l ^ k) (TT P r n) (TT P r' n) fun T (x : T.1.obj.Acr n) hx => mem_TT.2 (by
    have := dividedPowerFiltration_pow_mul (B.DD false T.1.obj n) (ht T.1.obj n) h (mem_TT.1 hx)
    rw [← map_pow] at this
    exact this)

theorem shT_tMor {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ) (y : MH P n j) :
    (shT ht P k h n).pull j ((tMor ht P r n).pull j y) = (tMor ht P r' n).pull j y :=
  mulSub_mulTo (TT P r n) (TT P r' n) (tA l ^ r) (tA l ^ k) (tA l ^ r') _ _ _ (by rw [← pow_add, add_comm, h]) j y

variable {P}

def galT (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n : ℕ) : CH.Mor (TT P r n).fn (TT P r n).fn (ACris.galCris σ) :=
  subMor (galMor σ a n) (TT P r n) (TT P r n) fun T x hx =>
    mem_TT.2 (Pb.dividedPowerFiltration_map (GlobalTheory.CompanionTheory.BetaGal.dd_twAcr false σ T.1.obj n) r ((mem_TT (T := (elTw σ a).obj T)).1 hx))

theorem galT_tMor (σ : Gal(PadicAlgCl l/K)) (a : P ⟶ twF σ ⋙ P) (r n j : ℕ) (y : MH P n j) :
    (galT σ a r n).pull j ((tMor ht P r n).pull j y) = χA σ ^ r • (tMor ht P r n).pull j ((galMor σ a n).pull j y) :=
  sub_mulTo (galMor σ a n) (TT P r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) (χA σ ^ r) _
    (by rw [map_pow, galCris_tA, mul_pow]) j y

def pullT' {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n : ℕ) : CH.Mor (TT P' r n).fn (TT P r n).fn (RingHom.id _) :=
  subMor (pullMor u n) (TT P' r n) (TT P r n) fun T x hx => mem_TT.2 ((mem_TT (T := (elMap u).obj T)).1 hx)

theorem pullT_tMor {P' : PAlg l ⥤ Type} (u : P ⟶ P') (r n j : ℕ) (y : MH P' n j) :
    (pullT' u r n).pull j ((tMor ht P' r n).pull j y) = (tMor ht P r n).pull j ((pullMor u n).pull j y) :=
  (sub_mulTo (pullMor u n) (TT P' r n) (TT P r n) _ (tA l ^ r) _ (tA l ^ r) 1 _ (one_mul _).symm j y).trans (one_smul _ _)

end P

section F
variable {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l)

theorem β_sh (ht : TFil l) {r r' : ℕ} (k : ℕ) (h : r + k = r') (n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r' n).pull j ((pdSh (B.Lc F κ false n) ((base l).cris n) (ht (base l) n) k h).pull j x) =
      (shT ht (F.pt κ) k h n).pull j ((βMorF F κ r n).pull j x) :=
  sub_mulSub (B.βMor F κ false n) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r')
    (TT (F.pt κ) r n) (TT (F.pt κ) r' n) _ _ (tA l ^ k) _ (tA l ^ k) _ rfl j x

theorem β_galF (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (r n j : ℕ)
    (x : CH.H (B.pdS (B.Lc F κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).pull j x) =
      (galT σ (B.ptTw F κ σ hσ) r n).pull j ((βMorF F κ r n).pull j x) := by
  have h1 := pull_pull (ACris.galCris σ) (pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r)
    (βMorF F κ r n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMorF F κ r n) (galT σ (B.ptTw F κ σ hσ) r n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (pd_pull_eq ((βMorF F κ r n).comp (σ'' := ACris.galCris σ) (galT σ (B.ptTw F κ σ hσ) r n))
    ((pdOm (CrystallineSemistableComparison.SH.galM F κ σ hσ false n) (ACris.galCris σ) (galBase_cris σ n) r).comp (σ'' := ACris.galCris σ) (βMorF F κ r n))
    (GlobalTheory.CompanionTheory.BetaGal.etaGal F κ σ hσ false n) (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ _ _ => rfl) j x).symm

variable {F} {F' : B.Fn O}

theorem β_pullF (u : B.Fn.Map F F') (r n j : ℕ) (x : CH.H (B.pdS (B.Lc F' κ false n) ((base l).cris n) r).fn j) :
    (βMorF F κ r n).pull j ((pdOm (CrystallineSemistableComparison.SH.pullM κ u false n) (RingHom.id _) (CrystallineSemistableComparison.SH.idc _) r).pull j x) =
      (pullT' (u.pt κ) r n).pull j ((βMorF F' κ r n).pull j x) :=
  sub_square (RingHom.id _) (B.pullMorC κ u false n) (B.βMor F κ false n) (B.βMor F' κ false n) (pullMor (u.pt κ) n)
    (B.pdS (B.Lc F' κ false n) ((base l).cris n) r) (B.pdS (B.Lc F κ false n) ((base l).cris n) r) (TT (F.pt κ) r n) (TT (F'.pt κ) r n)
    _ _ _ _ (GlobalTheory.CompanionTheory.BetaPull.cmpNat κ u false n) (fun _ _ => rfl) j x

end F

end CrystallineSemistableComparison.HT
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.HomP

open Pb

section Gen
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {F₁ : C₁ ⥤ ModuleCat.{0} R₁} {F₂ : C₂ ⥤ ModuleCat.{0} R₂} {F₃ : C₃ ⥤ ModuleCat.{0} R₃} {F₄ : C₄ ⥤ ModuleCat.{0} R₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}

theorem sq4 (m₁ : CH.Mor F₁ F₂ σ₁) (m₂ : CH.Mor F₂ F₄ σ₂) (m₃ : CH.Mor F₁ F₃ σ₃) (m₄ : CH.Mor F₃ F₄ σ₄)
    (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hτ : ∀ (T : C₄) (x : F₁.obj (m₁.G.obj (m₂.G.obj T))),
      m₄.τ T (m₃.τ _ ((F₁.map (η.app T)).hom x)) = m₂.τ T (m₁.τ _ x)) (j : ℕ) (x : CH.H F₁ j) :
    m₂.pull j (m₁.pull j x) = m₄.pull j (m₃.pull j x) := by
  haveI : RingHomCompTriple σ₁ σ₂ (σ₂.comp σ₁) := ⟨rfl⟩
  haveI : RingHomCompTriple σ₃ σ₄ (σ₂.comp σ₁) := ⟨RingHom.ext hσ⟩
  rw [pull_pull (σ₂.comp σ₁), pull_pull (σ₂.comp σ₁)]
  exact CrystallineSemistableComparison.P.prism (m₁.comp m₂) (m₃.comp m₄) η hτ j x

def smulMor (c : R₂) (m : CH.Mor F₁ F₂ σ₁) : CH.Mor F₁ F₂ σ₁ where
  G := m.G
  τ T := { toFun := fun x => c • m.τ T x
           map_add' := fun x y => by rw [map_add (f := _), smul_add]
           map_smul' := fun r x => by rw [LinearMap.map_smulₛₗ, smul_comm] }
  nat φ x := by
    change c • m.τ _ _ = (F₂.map φ).hom (c • m.τ _ x)
    rw [m.nat, map_smul]

theorem smulMor_pull (c : R₂) (m : CH.Mor F₁ F₂ σ₁) (j : ℕ) (x : CH.H F₁ j) : (smulMor c m).pull j x = c • m.pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

end Gen

section Nl
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def nlHom {T T' : Thick (nlFun γ p X q κ)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r) (dp : IsDPMorphism T.δ T'.δ φ)
    (hpt : ∀ h, Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ h)) ≫ pt T = pt T') : T ⟶ T' :=
  mkH φ comm dp (Ideal.map_le_iff_le_comap.1 dp.1) (Subtype.ext (Prod.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun r => by
    have h1 : (show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T.J (T.i r) := T.w r
    have h2 : (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk T'.J (T'.i r) := T'.w r
    change Ideal.quotientMap T'.J φ (Ideal.map_le_iff_le_comap.1 dp.1) ((show PtOver X q κ _ from T.y).1.1 (Ideal.Quotient.mk _ r)) =
      (show PtOver X q κ _ from T'.y).1.1 (Ideal.Quotient.mk _ r)
    rw [h1, h2, Ideal.quotientMap_mk, comm])) (hpt _)))

theorem spec_id {B₀ : Type} [CommRing B₀] (J : Ideal B₀) (h) {Z : Scheme.{0}} (y : Spec (CommRingCat.of (B₀ ⧸ J)) ⟶ Z) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B₀) h)) ≫ y = y := by
  have e : Ideal.quotientMap J (RingHom.id B₀) h = RingHom.id _ := by ext; rfl
  rw [e, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end Nl

section S
variable {R₁ R₂ R₃ R₄ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing R₄]
  {C₁ C₂ C₃ C₄ : Type 1} [Category.{0} C₁] [Category.{0} C₂] [Category.{0} C₃] [Category.{0} C₄]
  {Φ₁ : PDF R₁ C₁} {Φ₂ : PDF R₂ C₂} {Φ₃ : PDF R₃ C₃} {Φ₄ : PDF R₄ C₄}
  {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₄} {σ₃ : R₁ →+* R₃} {σ₄ : R₃ →+* R₄}
  (m₁ : SMor Φ₁ Φ₂ σ₁) (m₂ : SMor Φ₂ Φ₄ σ₂) (m₃ : SMor Φ₁ Φ₃ σ₃) (m₄ : SMor Φ₃ Φ₄ σ₄)
  {a₁ b₁ : IdF Φ₁.A} {a₂ b₂ : IdF Φ₂.A} {a₃ b₃ : IdF Φ₃.A} {a₄ b₄ : IdF Φ₄.A}

theorem genA (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.Le a₁ a₂) (k₁ : m₁.Le b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.Le a₃ a₄) (k₄ : m₄.Le b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sq h₁ k₁).pull j x) = (m₄.sq h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine sq4 (m₁.sq h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (m₄.sq h₄ k₄) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) (hρ T y))

theorem genB (c₁ : R₂) (c c₄ : R₄) (hσ : ∀ a, σ₄ (σ₃ a) = σ₂ (σ₁ a)) (hc : σ₂ c₁ = c * c₄) (η : m₂.G ⋙ m₁.G ⟶ m₄.G ⋙ m₃.G)
    (hρ : ∀ (T : C₄) (x : Φ₁.A.obj (m₁.G.obj (m₂.G.obj T))), m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom x)) = m₂.ρ T (m₁.ρ _ x))
    (h₁ : m₁.LeC c₁ a₁ a₂) (k₁ : m₁.LeC c₁ b₁ b₂) (h₂ : m₂.Le a₂ a₄) (k₂ : m₂.Le b₂ b₄) (h₃ : m₃.Le a₁ a₃) (k₃ : m₃.Le b₁ b₃)
    (h₄ : m₄.LeC c₄ a₃ a₄) (k₄ : m₄.LeC c₄ b₃ b₄) (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (m₂.sq h₂ k₂).pull j ((m₁.sqC c₁ h₁ k₁).pull j x) = c • (m₄.sqC c₄ h₄ k₄).pull j ((m₃.sq h₃ k₃).pull j x) := by
  refine Eq.trans ?_ (smulMor_pull c (m₄.sqC c₄ h₄ k₄) j _)
  refine sq4 (m₁.sqC c₁ h₁ k₁) (m₂.sq h₂ k₂) (m₃.sq h₃ k₃) (smulMor c (m₄.sqC c₄ h₄ k₄)) hσ η (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  have e : c • (algebraMap R₄ _ c₄ * m₄.ρ T (m₃.ρ _ ((Φ₁.A.map (η.app T)).hom y))) =
      m₂.ρ T (algebraMap R₂ _ c₁ * m₁.ρ (m₂.G.obj T) y) := by
    rw [hρ, map_mul, m₂.comm, hc, map_mul, Algebra.smul_def, mul_assoc]
  exact Subtype.ext (congrArg (Ideal.Quotient.mk _) e)

theorem genC {a₁' b₁' : IdF Φ₁.A} {a₂' b₂' : IdF Φ₂.A} (h : m₁.Le a₁ a₂) (k : m₁.Le b₁ b₂) (h' : m₁.Le a₁' a₂') (k' : m₁.Le b₁' b₂')
    (e₁ : ∀ T, a₁.S T ≤ a₁'.S T) (f₁ : ∀ T, b₁.S T ≤ b₁'.S T) (e₂ : ∀ T, a₂.S T ≤ a₂'.S T) (f₂ : ∀ T, b₂.S T ≤ b₂'.S T)
    (j : ℕ) (x : CH.H (sq a₁ b₁) j) :
    (sqLe e₂ f₂).pull j ((m₁.sq h k).pull j x) = (m₁.sq h' k').pull j ((sqLe e₁ f₁).pull j x) := by
  refine sq4 (m₁.sq h k) (sqLe e₂ f₂) (sqLe e₁ f₁) (m₁.sq h' k') (fun _ => rfl) (𝟙 m₁.G) (fun T x => ?_) j x
  obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
  refine Subtype.ext (congrArg (Ideal.Quotient.mk _) ?_)
  change m₁.ρ T ((Φ₁.A.map (𝟙 _)).hom y) = m₁.ρ T y
  rw [Φ₁.A.map_id]
  rfl

end S

section D
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ}
  {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)} {s s' : ℕ} {sA : A →+* A'}
  (nm : NMor γ q (κA O I) γ' q' (κA O I') sA)
  (hm : ∀ T, TS γ' q' l s' {⊤} T → TS γ q l s {⊤} ((nm.mor 0).obj T))
  (d : RedIn δ κ γ l n) (d' : RedIn δ κ γ' l n) {σ : R →+* R}
  (hd : ∀ (x : R) (a : A), d.ρ x = Ideal.Quotient.mk _ a → d'.ρ (σ x) = Ideal.Quotient.mk _ (sA a))
  (mm : GlobalTheory.LogCris.Mor (nlFun δ l X q κ) (nlFun δ l X' q' κ) σ)
  (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (nlFun δ l X' q' κ).Pt.obj B₀),
    (show PtOver X q κ B₀ from mm.pt.app B₀ y).1.2 = (show PtOver X' q' κ B₀ from y).1.2 ≫ nm.u)

theorem std_le (r : ℤ) : (nm.smor _ _ hm).Le (stdI (TS γ q l s {⊤}) (some r) ((l : A) ^ n)) (stdI (TS γ' q' l s' {⊤}) (some r) ((l : A') ^ n)) := by
  intro T x hx
  have e : T.obj.i (sA ((l : A) ^ n)) = T.obj.i ((l : A') ^ n) := by rw [map_pow sA, map_natCast]
  have hx' : (show T.obj.B from x) ∈ T.obj.pdPow r.toNat ⊔ Ideal.span {T.obj.i (sA ((l : A) ^ n))} := hx
  rw [e] at hx'
  exact hx'

include hd in
theorem r_comm (T : Thick (nlFun γ' 0 X' q' (κA O I'))) (x : R) :
    iBar ((nm.mor 0).obj T) l n (d.ρ x) = iBar T l n (d'.ρ (σ x)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d.ρ x)
  rw [hd x a ha.symm, ← ha]
  rfl

def rEta (T : (TS γ' q' l s' {⊤}).FullSubcategory) :
    (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T) ⟶ mm.obj ((redG q' s' d' {⊤}).obj T) :=
  nlHom (T := (redG q s d {⊤}).obj ((nm.smor _ _ hm).G.obj T)) (T' := mm.obj ((redG q' s' d' {⊤}).obj T))
    (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) (r_comm nm d d' hd T.obj)
    (DPMorphism.id (redδ T.obj T.property.1 n)).isDPMorphism fun e => (spec_id _ e _).trans
      ((Category.assoc _ _ _).symm.trans (hpt _ ((redG q' s' d' {⊤}).obj T).y).symm)

def rNat : (nm.smor _ _ hm).G ⋙ redG q s d {⊤} ⟶ redG q' s' d' {⊤} ⋙ mm.functor where
  app := rEta nm hm d d' hd mm hpt
  naturality T T' f := hom_ext (show (RingHom.id (T'.obj.B ⧸ lnT T'.obj l n)).comp (lnMap f.hom.φ l le_rfl) =
    (lnMap f.hom.φ l le_rfl).comp (RingHom.id (T.obj.B ⧸ lnT T.obj l n)) from rfl)

include hd hpt in
theorem genD {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (lam' : Λ →+* A') (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))
    (hc' : ∀ a, d'.ρ (c a) = Ideal.Quotient.mk _ (lam' a)) (sΛ : Λ →+* Λ) (hs : ∀ a, σ (c a) = c (sΛ a))
    (hl : ∀ a, lam' (sΛ a) = sA (lam a)) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ l X q κ) c r).fn j) :
    ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1))).pull j ((redSub q s {⊤} d c lam hc r).pull j x) =
      (redSub q' s' {⊤} d' c lam' hc' r).pull j ((pdOm (c := c) (c' := c) mm sΛ hs r).pull j x) := by
  have key := sq4 (F₁ := (B.pdS (nlFun δ l X q κ) c r).fn) (F₃ := (B.pdS (nlFun δ l X' q' κ) c r).fn)
    (redSub q s {⊤} d c lam hc r) ((nm.smor _ _ hm).sq (std_le nm hm (r : ℤ)) (std_le nm hm ((r : ℤ) + 1)))
    (pdOm (L := nlFun δ l X q κ) (L' := nlFun δ l X' q' κ) (c := c) (c' := c) mm sΛ hs r) (redSub q' s' {⊤} d' c lam' hc' r) hl
    (rNat nm hm d d' hd mm hpt)
  refine key (fun T x => ?_) j x
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
  exact Subtype.ext rfl

end D

end CrystallineSemistableComparison.HT.HomP
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

structure RhoEx : Prop where
  ex : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m → ∀ x : Y.Fam M r j, CB.Comp x → ∃! w, L.Rho x w
  add : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (x y : Y.Fam M r j) w w', L.Rho x w → L.Rho y w' → L.Rho (x + y) (w + w')
  smul : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (c • x) (L.ι (L.lam c) • w)

def CoEx : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), M.Sm → ∀ r j : ℕ, r < m →
  Spans L.γB M.q (L.QB M) L.tB_mem r j ∧ ∃ co, IsCo L.γB M.q (L.QB M) L.θ L.tB_mem r j co

def HomRho : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (mm : ∀ n, GlobalTheory.LogCris.Mor (Y.L N n) (Y.L M n) (sn n)),
  (∀ (n : ℕ) (B₀ : CommRingCat.{0}) (y : (Y.L M n).Pt.obj B₀), ((mm n).pt.app B₀ y).1.2 = (show Spec B₀ ⟶ M.X from y.1.2) ≫ u) →
  ∀ (r j : ℕ) (x : Y.Fam N r j) (w : HG (L.QB N) r j), L.Rho x w →
    L'.Rho (M := M) (fun n => (pdOm (mm n) sΛ (h.cris n) r).pull j (x n)) (h.fW u hu r j w)

def HomMu : Prop := ∀ {Y : CB l K} {m m' : ℕ} {L : Lv Y m} {L' : Lv Y m'} {sΛ : Y.Λ →+* Y.Λ}
  {sn : ∀ n, Y.R n →+* Y.R n} {sC : ℂ_[l] →+* ℂ_[l]} {c : ℂ_[l]} (h : LHom L L' sΛ sn sC c) {M N : Model l K}
  (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a r j : ℕ) (y : Hdg N.q a j),
    h.fW u hu r j (L.μ N a r j y) = h.cB ^ (r - a) • L'.μ M a r j (pullH (Model.genMap u hu) (Model.genMap_q u hu) a j y)

structure MulRho : Prop where
  sh : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (x : Y.Fam M r j) w, L.Rho x w →
    L.Rho (CB.shS k h x) (shG (L.QB M) L.tB_mem k h j w)
  sh_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' j : ℕ} (k : ℕ) (h : r + k = r') (a : ℕ), a ≤ r → ∀ y : Hdg M.q a j,
    shG (L.QB M) L.tB_mem k h j (L.μ M a r j y) = L.μ M a r' j y
  cup : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j : ℕ} (h : r + r' = s) (x : Y.Fam M r i) (y : Y.Fam M r' j) w w',
    L.Rho x w → L.Rho y w' → L.Rho (CB.cupS h x y) (cupG (L.QB M) h w w')
  cup_μ : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K) {r r' s i j a a' c : ℕ} (h : r + r' = s) (ha : a + a' = c), a ≤ r → a' ≤ r' →
    ∀ (y : Hdg M.q a i) (y' : Hdg M.q a' j),
    cupG (L.QB M) h (L.μ M a r i y) (L.μ M a' r' j y') = L.μ M c s (i + j) (cupH M.q ha rfl y y')
  one : ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), L.Rho (Y.oneS M) (L.μ M 0 0 0 (oneH M.q))

def FirstChernHodgeTateCompat : Prop := ∀ {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K), 1 < m → ∀ (D : E.LineData M.X), sSup (𝒱D D) = ⊤ →
  ∀ (x : Y.Fam M 1 2) (c : Hdg M.q 1 2), CB.IsFirstChernClassInFamily D x → IsDlogFirstChernClass M.q (genD D) c → L.Rho x (L.μ M 1 1 2 c)

end CrystallineSemistableComparison.HT
end
end
