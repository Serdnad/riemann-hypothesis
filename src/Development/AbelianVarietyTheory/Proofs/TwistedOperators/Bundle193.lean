module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle179
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle180
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle181
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle178
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftEquivariance

theorem commutes_adjoint {G E E' : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    (ρ : Representation ℂ G E) (ρ' : Representation ℂ G E') (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (hρ' : ∀ g x, ‖ρ' g x‖ = ‖x‖)
    (f : E →ₗ[ℂ] E') (hf : Commutes ρ ρ' f) : Commutes ρ' ρ (LinearMap.adjoint f) := by
  intro g y
  have i1 : ∀ u v, inner ℂ (ρ g u) (ρ g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ g) (hρ g)).inner_map_map u v
  have i2 : ∀ u v, inner ℂ (ρ' g u) (ρ' g v) = inner ℂ u v :=
    fun u v => (LinearIsometry.mk (ρ' g) (hρ' g)).inner_map_map u v
  refine ext_inner_left ℂ fun x => ?_
  have e : x = ρ g (ρ g⁻¹ x) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e, i1, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right, hf g, i2]

section Generic

variable {Γ Gf W G : Type} [Group Γ] [Group Gf] [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem translate_indep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) {F : Gf → W}
    (hF : F ∈ Bridge.AdForms ι ρ l.J l.χ) (κ κ' : l.Q) (hk : ((κ⁻¹ * κ' : l.Q) : Gf) ∈ l.J) (h : Gf) :
    (((l.ch κ')⁻¹ : ℂˣ) : ℂ) • F (h * κ') = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • F (h * κ) := by
  have e := hF 1 (h * κ) ⟨_, hk⟩
  have e1 : ι 1 * (h * κ) * ((κ⁻¹ * κ' : l.Q) : Gf) = h * κ' := by simp [mul_assoc]
  have e2 : l.χ ⟨_, hk⟩ = (l.ch κ)⁻¹ * l.ch κ' := by
    rw [← l.ch_J, ← map_inv, ← map_mul]
  simp only at e
  rw [e1, e2, map_one, Module.End.one_apply] at e
  rw [e, smul_smul, ← Units.val_mul, mul_comm (l.ch κ)⁻¹, inv_mul_cancel_left]

theorem exists_rep (ι : Γ →* Gf) (ρ : Γ →* Module.End ℂ W) (l : Bridge.LevDatG Gf) (M : HMod (Gf → W))
    (hinj : Function.Injective M.e) (hM : ∀ x, M.e x ∈ Bridge.AdForms ι ρ l.J l.χ)
    (hT : ∀ (κ : l.Q) (x : M.H), ∃ x' : M.H, (∀ h, M.e x' h = ((l.ch κ : ℂˣ) : ℂ)⁻¹ • M.e x (h * κ)) ∧ ‖x'‖ = ‖x‖)
    (red : l.Q →* G) (hs : Function.Surjective red) (hker : ∀ κ, red κ = 1 → (κ : Gf) ∈ l.J) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧
      ∀ κ x h, M.e (π (red κ) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := by
  choose s hs using hs
  choose T hT hn using hT
  have key : ∀ κ x h, M.e (T (s (red κ)) x) h = (((l.ch κ)⁻¹ : ℂˣ) : ℂ) • M.e x (h * κ) := fun κ x h => by
    rw [hT, ← Units.val_inv_eq_inv_val]
    exact translate_indep ι ρ l (hM x) κ _ (hker _ (by rw [map_mul, map_inv, hs, inv_mul_cancel])) h
  let L : G → M.H →ₗ[ℂ] M.H := fun g =>
    { toFun := T (s g)
      map_add' := fun x y => hinj (funext fun h => by
        rw [map_add (f := _), Pi.add_apply, hT, hT, hT, map_add (f := _), Pi.add_apply, smul_add])
      map_smul' := fun a x => hinj (funext fun h => by
        rw [map_smul, Pi.smul_apply, hT, hT, map_smul, Pi.smul_apply, smul_comm]; rfl) }
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := fun g g' => ?_ }, fun g x => hn _ x, key⟩
  · ext x
    refine hinj (funext fun h => ?_)
    have := key 1 x h
    rw [map_one] at this
    exact this.trans (by simp)
  · ext x
    refine hinj (funext fun h => ?_)
    have := key (s g * s g') x h
    rw [map_mul, hs, hs] at this
    refine this.trans ?_
    show _ = M.e (T (s g) (T (s g') x)) h
    rw [hT, hT, smul_smul, map_mul, Subgroup.coe_mul, mul_assoc]
    simp [mul_comm]

end Generic

variable {D : D7}

theorem mem_parLev {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) : Formalism.UG.bc (swapAE D) x.1 ∈ parLev D.sp.cm V.gram β L := by
  have h1 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flagL L) := h
  exact h1.1

theorem mem_J {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x : Bridge.Gf V}
    (h : x ∈ (levEnv V β L).Q) (h1 : rTup β L (Formalism.UG.bc (swapAE D) x.1) = 1) : x ∈ (levEnv V β L).J := by
  have h2 : rTup β L (Formalism.UG.bc (swapAE D) x.1) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := Subgroup.mem_bot.2 h1
  have h3 : Formalism.UG.bc (swapAE D) x.1 ∈ lev D.sp.cm V.gram β (flag1L L) := ⟨mem_parLev h, h2⟩
  exact h3

theorem rTup_bc_mul {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {x y : Bridge.Gf V}
    (hx : x ∈ (levEnv V β L).Q) (hy : y ∈ (levEnv V β L).Q) :
    rTup β L (Formalism.UG.bc (swapAE D) (x * y).1) =
      rTup β L (Formalism.UG.bc (swapAE D) x.1) * rTup β L (Formalism.UG.bc (swapAE D) y.1) := by
  rw [Subgroup.coe_mul, map_mul]
  exact rTup_mul (mem_parLev hx) (mem_parLev hy)

def redHom (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    (levEnv V β L).Q →* G0 L.Pg L.r :=
  MonoidHom.mk' (fun κ => rTup β L (Formalism.UG.bc (swapAE D) κ.1.1)) fun a b => rTup_bc_mul a.2 b.2

theorem redHom_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} {κ : (levEnv V β L).Q}
    {g₀ : G0 L.Pg L.r} : LiftsTo V β L κ g₀ ↔ redHom V β L κ = g₀ := Iff.rfl

theorem exists_transRep (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V) (hc : c.Is)
    (M : HMod (Bridge.Gf V → c.W)) {I : Type} [Fintype I] (y : I → Bridge.Gf V)
    (hy : Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y)
    (hM : M.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
      (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y))
    {G : Type} [Group G] (eG : G ≃* G0 L.Pg L.r) (hs : ∀ g, ∃ κ, LiftsTo V β L κ (eG g)) :
    ∃ π : Representation ℂ G M.H, (∀ g x, ‖π g x‖ = ‖x‖) ∧ IsTransRep V β L eG M π := by
  have hred : ∀ κ g, LiftsTo V β L κ (eG g) → (eG.symm.toMonoidHom.comp (redHom V β L)) κ = g := fun κ g h =>
    eG.symm_apply_eq.2 (redHom_eq.1 h)
  have h1 : ∀ x, M.e x ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ :=
    fun x => hM.2.1.le ⟨x, rfl⟩
  have h2 := ClassSumTranslate.translate_model (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L)
    (fun γ u v => hc.2.1 _ u v) (ClassSumTranslate.levEnv_normal V β L) (fun q => ClassSumTranslate.norm_levFn V β L _) hy M hM
  have h3 : Function.Surjective (eG.symm.toMonoidHom.comp (redHom V β L)) := fun g => (hs g).imp fun κ h => hred κ g h
  have h4 : ∀ κ, (eG.symm.toMonoidHom.comp (redHom V β L)) κ = 1 → (κ : Bridge.Gf V) ∈ (levEnv V β L).J := fun κ h =>
    mem_J κ.2 (redHom_eq.2 (eG.symm.injective (h.trans (map_one eG.symm).symm)))
  refine (exists_rep (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L) M hM.1 h1 h2 _ h3 h4).imp
    fun π hπ => ⟨hπ.1, fun g x => ⟨hs g, fun κ hκ h => ?_⟩⟩
  exact (congrArg (fun g' => M.e (π g' x) h) (hred κ g hκ)).symm.trans (hπ.2 κ x h)

theorem exists_rangeRestrict_eq {G H : Type} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : ∀ g, ∃ a ∈ f.ker, ∃ k ∈ K, g = a * k) (x : f.range) : ∃ k ∈ K, f.rangeRestrict k = x := by
  obtain ⟨_, g, rfl⟩ := x
  obtain ⟨a, ha, k, hk, rfl⟩ := h g
  refine ⟨k, hk, Subtype.ext ?_⟩
  show f k = f (a * k)
  rw [map_mul, MonoidHom.mem_ker.1 ha, one_mul]

theorem exists_fin_lift (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, (finHom V).rangeRestrict k = x :=
  exists_rangeRestrict_eq (finHom V) (GfC V) (GlobalTheory.UnitarySplit.real_finite_split D V).1 x

theorem ch_eq {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (q : (levEnv V β L).Q) :
    (levEnv V β L).ch q = levFn β (flagL L) (Formalism.UG.bc (swapAE D) q.1.1) := rfl

theorem exists_adelic_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {g₀ : G0 L.Pg L.r} {F F' : Bridge.Gf V → W}
    (h : IsTranslate V β L g₀ F F') :
    ∃ κ, IsLevelLift V β L g₀ κ ∧ ∀ x, F' x = (levChi V β (flagL L) κ)⁻¹ • F (x * (finHom V).rangeRestrict κ) := by
  refine h.1.elim fun q hl => (exists_fin_lift V q.1).imp fun k hk => ?_
  have e0 : finHom V k = q.1.1 := congrArg Subtype.val hk.2
  have e1 : finE V k = Formalism.UG.bc (swapAE D) q.1.1 := (finE_eq V k).trans (congrArg (Formalism.UG.bc (swapAE D)) e0)
  have hl1 : rTup β L (Formalism.UG.bc (swapAE D) q.1.1) = g₀ := hl
  have hc : levChi V β (flagL L) k = (((levEnv V β L).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn β (flagL L)) e1).trans (ch_eq q).symm)
  have hp : finE V k ∈ parLev D.sp.cm V.gram β L := e1.symm ▸ mem_parLev q.2
  refine ⟨⟨hk.1, hp, (congrArg (rTup β L) e1).trans hl1⟩, fun x => (h.2 q hl x).trans ?_⟩
  exact congrArg₂ (fun (a : ℂ) (z : Bridge.Gf V) => a • F (x * z))
    ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hc.symm)) hk.2.symm

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end GlobalTheory.LiftEquivariance

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.FockSrcDec

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  classical

  conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv {σ : Type} (b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  by_cases h : MvPolynomial.pderiv b P = 0
  · simp [h]
  · have := deg_X_pderiv b b P
    rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) h] at this
    omega

theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b (MvPolynomial.X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (MvPolynomial.totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (MvPolynomial.totalDegree_smul_le _ _).trans (h P)

theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i : Fin b) (j k : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' i ≠ ε k then
    (sgn (ε j) * sgn (ε k)) • (MvPolynomial.X (τ, i, j) * MvPolynomial.X (τ, i, k)) else 0

theorem quad_hom (i : Fin b) (j k : Fin a) : (quad τ ε ε' i j k).IsHomogeneous 2 := by
  unfold quad
  split_ifs
  · exact (MvPolynomial.homogeneousSubmodule _ ℂ 2).smul_mem _
      ((MvPolynomial.isHomogeneous_X ℂ _).mul (MvPolynomial.isHomogeneous_X ℂ _))
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem term_mem (i : Fin b) (j k : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' i k - LinearMap.mulLeft ℂ (quad τ ε ε' i j k) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' i = ε k
  · rw [if_pos h1, if_pos h2, if_neg (fun h => h.2 h2), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm]
    exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => deg_X_pderiv _ _ P)
  · rw [if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩]
    convert Submodule.zero_mem _
    rw [sub_eq_zero]
    refine LinearMap.ext fun P => ?_
    simp [smul_smul, mul_assoc, mul_comm (sgn (ε k))]
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => (deg_pderiv _ _).trans (deg_pderiv _ P)))
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => deg_pderiv_X _ _ P))

def quadS (X : Matrix (Fin a) (Fin a) ℂ) : PolF D b a :=
  ∑ j, ∑ k, X j k • ∑ i, quad τ ε ε' i j k

theorem quadS_hom (X : Matrix (Fin a) (Fin a) ℂ) : (quadS τ ε ε' X).IsHomogeneous 2 :=
  (MvPolynomial.homogeneousSubmodule _ ℂ 2).sum_mem fun j _ =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ <|
      Submodule.sum_mem _ fun i _ => quad_hom τ ε ε' i j k

theorem rest_mem (X : Matrix (Fin a) (Fin a) ℂ) :
    fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X) ∈ nonRaising (FVar D b a) := by
  have h : LinearMap.mulLeft ℂ (quadS τ ε ε' X) =
      ∑ j, ∑ k, X j k • ∑ i, LinearMap.mulLeft ℂ (quad τ ε ε' i j k) := by
    refine LinearMap.ext fun P => ?_
    simp [quadS, Finset.sum_mul, LinearMap.sum_apply]
  rw [h, fockS, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
  rw [add_sub_right_comm]
  refine Submodule.add_mem _ (term_mem τ ε ε' i j k) ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => le_rfl)
  · exact Submodule.zero_mem _

theorem sgn_ne_zero (e : Bool) : sgn e ≠ 0 := by
  cases e <;> simp [sgn]

theorem quadS_ne_zero (X : Matrix (Fin a) (Fin a) ℂ) (i : Fin b) (j k : Fin a) (hj : ε' i = ε j)
    (hk : ε' i ≠ ε k) (hX : X j k ≠ 0) : quadS τ ε ε' X ≠ 0 := by
  classical
  intro h0
  let f : FVar D b a → ℂ := fun v => if v = (τ, i, j) ∨ v = (τ, i, k) then 1 else 0
  have key : ∀ i' j' k', MvPolynomial.aeval f (quad τ ε ε' i' j' k') =
      if i' = i ∧ j' = j ∧ k' = k then sgn (ε j) * sgn (ε k) else 0 := by
    intro i' j' k'
    by_cases h : i' = i ∧ j' = j ∧ k' = k
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [quad, hj, f, hj ▸ hk]
    · rw [if_neg h]
      unfold quad
      split_ifs with h'
      · simp only [map_smul, map_mul, MvPolynomial.aeval_X, f, Prod.mk.injEq, true_and]
        split_ifs with h1 h2
        · exfalso
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact h'.2 hj
          · exact h ⟨rfl, rfl, rfl⟩
          · exact hk h'.1
          · exact hk h'.1
        all_goals simp
      · simp
  have h1 := congrArg (MvPolynomial.aeval f) h0

  simp only [quadS, map_sum, map_smul, key, map_zero] at h1
  rw [Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i] at h1
  · simp [hX, sgn_ne_zero] at h1
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp

theorem fockS_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X : Matrix (Fin a) (Fin a) ℂ), 0 < b → (∃ j k, ε j ≠ ε k ∧ X j k ≠ 0 ∧ X k j ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' X = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' X hb ⟨j, k, hjk, h1, h2⟩
  refine ⟨quadS τ ε ε' X, fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X), ?_, quadS_hom τ ε ε' X,
    mem_nonRaising.1 (rest_mem τ ε ε' X), by abel⟩
  by_cases h : ε' ⟨0, hb⟩ = ε j
  · exact quadS_ne_zero τ ε ε' X ⟨0, hb⟩ j k h (h ▸ hjk) h1
  · refine quadS_ne_zero τ ε ε' X ⟨0, hb⟩ k j ?_ h h2
    revert h hjk
    cases ε' ⟨0, hb⟩ <;> cases ε j <;> cases ε k <;> simp

end GlobalTheory.Chain.RealIt.FockSrcDec

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealIt.SubstDeg

theorem totalDegree_aeval_le {σ κ : Type*} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]

  rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (AddMonoidAlgebra.coeff P s)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_subst_le : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (g : Matrix (Fin a) (Fin a) ℂ) (k : Matrix (Fin b) (Fin b) ℂ) (P : PolF D b a), (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst τ ε ε' g k P).totalDegree ≤ P.totalDegree := by
  intro D a b τ ε ε' g k P
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.subst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs with h
  · refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
    refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le
  all_goals first
    | exact (MvPolynomial.totalDegree_X _).le
    | (refine MvPolynomial.totalDegree_finsetSum_le fun l _ => ?_
       refine MvPolynomial.totalDegree_finsetSum_le fun m _ => ?_
       exact (MvPolynomial.totalDegree_smul_le _ _).trans (MvPolynomial.totalDegree_X _).le)

end GlobalTheory.Chain.RealIt.SubstDeg
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = v → χ.UnrAt P) → UnramAt ε c := by
  first | exact @GlobalTheory.UnramOver.unramAt_of_unrAt | exact GlobalTheory.UnramOver.unramAt_of_unrAt | (intros; apply GlobalTheory.UnramOver.unramAt_of_unrAt <;> assumption)
end

section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary

theorem _root_.GlobalTheory.T.quotientIntegral_eq_zero_of_normalised_coset_integrals : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (T N : Subgroup H), IsClosed (T : Set H) → IsClosed (N : Set H) → IsMulCommutative T → (∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) → Topology.IsClosedEmbedding (fun p : N × T => (p.1 : H) * p.2) → ∀ (dh : Measure H) [dh.IsHaarMeasure] (dt : Measure T) [dt.IsHaarMeasure] (dn : Measure N) [dn.IsHaarMeasure] [dn.IsMulRightInvariant] (φ : H → ℂ), Measurable φ → LeftInv T φ → Integrable (descend T φ) (quotMeas T dt dh) → (∀ x, ∫ n : N, φ (n * x) ∂dn = 0) → quotInt T dt dh φ = 0 := by
  first | exact @GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | exact GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero | (intros; apply GlobalTheory.Orb.quotInt_eq_zero_of_integral_coset_eq_zero <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.quadraticPowerCharacter_splitPlaces_values_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (w w' : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = w'.under (𝓞 F) → w ≠ w' → UnrAt μ w → UnrAt μ w' → val μ w * val μ w' = 1 := by
  first | exact @GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | exact GlobalTheory.LFun.SplitVal.val_mul_val_eq_one | (intros; apply GlobalTheory.LFun.SplitVal.val_mul_val_eq_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.sq_value_eq_one_at_inert_place_of_restrictsToQuadratic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (μ : (TensorProduct F (AF F) E)ˣ →* Circle) (b : ℕ), ResEta F E μ b → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w → UnrAt μ w → val μ w ^ 2 = 1 := by
  first | exact @GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | exact GlobalTheory.LFun.val_sq_eq_one_of_isInertAt | (intros; apply GlobalTheory.LFun.val_sq_eq_one_of_isInertAt <;> assumption)
end

section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

theorem _root_.GlobalTheory.T.gelfand_pair_spherical_vector_unique : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first | exact @GlobalTheory.fixed_eq_span_of_gelfandPair | exact GlobalTheory.fixed_eq_span_of_gelfandPair | (intros; apply GlobalTheory.fixed_eq_span_of_gelfandPair <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_levi_phase_change_of_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  first | exact @GlobalTheory.LeviNorm.integral_phase_sandwich | exact GlobalTheory.LeviNorm.integral_phase_sandwich | (intros; apply GlobalTheory.LeviNorm.integral_phase_sandwich <;> assumption)
end
