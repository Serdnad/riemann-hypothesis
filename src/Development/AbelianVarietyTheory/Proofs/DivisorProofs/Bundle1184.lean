module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle108
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.HnStepEqOfNorm
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct

namespace GlobalTheory.ThetaFiresLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S'] [AddCommGroup Sinf] [Module ℂ Sinf]
  [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]

theorem exists_isThetaP (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by
  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν) ?_ ?_ ?_ ?_, hint,
    fun f e g => rfl⟩
  · intro f f' e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    exact integral_add (hint f e g) (hint f' e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
    exact integral_smul c _
  · intro f e e'
    funext g
    simp only [Pi.add_apply, map_add (f := _), LinearMap.add_apply]
    exact integral_add (hint f e g) (hint f e' g)
  · intro c f e
    funext g
    simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply]
    exact integral_smul c _

theorem exists_isThetaP' (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 th pt io A thP := by
  obtain rfl : th = fun g h s => thL g h s := funext fun g => funext fun h => funext fun s => h1 g h s
  obtain rfl : pt = fun s => ptL s := funext h2
  exact exists_isThetaP ν 𝓕 thL ptL io A hint

theorem exists_linear_choice {X M N : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (W : Submodule ℂ M) (r : M →ₗ[ℂ] N) (u : X →ₗ[ℂ] N)
    (h : ∀ x, ∃ m ∈ W, r m = u x) : ∃ y : X →ₗ[ℂ] M, (∀ x, y x ∈ W) ∧ ∀ x, r (y x) = u x := by
  choose m hm hr using h
  let b := Module.Basis.ofVectorSpace ℂ X
  let y' : X →ₗ[ℂ] W := b.constr ℂ fun k => ⟨m (b k), hm _⟩
  refine ⟨W.subtype ∘ₗ y', fun x => (y' x).2, fun x => ?_⟩
  have : r ∘ₗ W.subtype ∘ₗ y' = u := b.ext fun k => by
    simp only [LinearMap.comp_apply, y', Module.Basis.constr_basis, Submodule.subtype_apply, hr]
  exact LinearMap.congr_fun this x

theorem exists_linear_lift {ι X : Type} [AddCommGroup X] [Module ℂ X] {M : ι → Type} [∀ a, AddCommGroup (M a)]
    [∀ a, Module ℂ (M a)] (low : ∀ a, Submodule ℂ (M a)) (W : Submodule ℂ ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)))
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' → ℂ) (pt : Sinf → S')
    (thL : G' → H' → S' →ₗ[ℂ] ℂ) (ptL : Sinf →ₗ[ℂ] S') (h1 : ∀ g h s, th g h s = thL g h s) (h2 : ∀ s, pt s = ptL s)
    (io : (⨂[ℂ] a, low a) →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (ext : X →ₗ[ℂ] (H' → Tau))
    (h : ∀ x, (∀ e g, IntegrableOn (fun h => th g h (pt (io e (ext x h)))) 𝓕 ν) ∧
      ∃ U ∈ W, ∀ v : ∀ a, low a, U (fun a => (v a : M a)) = Lift.thetaPInt ν 𝓕 th pt io (ext x) (PiTensorProduct.tprod ℂ v)) :
    ∃ y : X →ₗ[ℂ] ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)), (∀ x, y x ∈ W) ∧
      ∃ thP : LinearMap.range ext →ₗ[ℂ] ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)),
        Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range ext) thP ∧
          ∀ (x : X) (v : ∀ a, low a), y x (fun a => (v a : M a)) = thP (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) := by
  obtain ⟨thP, hP⟩ := exists_isThetaP' ν 𝓕 th pt thL ptL h1 h2 io (LinearMap.range ext) (by
    rintro ⟨_, x, rfl⟩ e g
    exact (h x).1 e g)
  let r : ((∀ a, M a) →ₘₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U fun a => (v a : M a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : ((⨂[ℂ] a, low a) →ₗ[ℂ] (G' → ℂ)) →ₗ[ℂ] ((∀ a, low a) → G' → ℂ) :=
    { toFun := fun U v => U (PiTensorProduct.tprod ℂ v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨y, hy, hr⟩ := exists_linear_choice W r (p ∘ₗ thP ∘ₗ ext.rangeRestrict) fun x => by
    obtain ⟨U, hU, hv⟩ := (h x).2
    exact ⟨U, hU, funext fun v => funext fun g =>
      (congrFun (hv v) g).trans (hP.eq (ext.rangeRestrict x) (PiTensorProduct.tprod ℂ v) g).symm⟩
  exact ⟨y, hy, thP, hP, fun x v => congrFun (hr x) v⟩

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelFiring

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def kernelL (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.proj (R := ℂ) (φ := fun _ : WO (Vc D i) (Wc D i) => ℂ) 0 ∘ₗ R.ωP i t (h, g)

end GlobalTheory.ThetaFiresLinear

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SecLift

section Lin

variable {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]


end Lin

section Model

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

end Model

section Act

open Formalism.IndefR.Lev

theorem actL_apply {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} {g0 : G0 L.Pg L.r}
    (hk : ∃ κ, IsLevelLift V β L g0 κ) (Φ : GA D V → ℂ) (h : GA D V) :
    Links.actL V β L g0 Φ h = (levChi V β (flagL L) hk.choose)⁻¹ * Φ (h * hk.choose) := by
  show actG0 V β L g0 Φ h = _
  rw [actG0, dite_eq_left hk]

theorem span_of_pres {G Γ W K H : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
    [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] (G → W))
    (hinj : Function.Injective e) (hr : LinearMap.range e = Bridge.AdForms ι ρ J χ) (j : S.Forms → H)
    (hj : ∀ x, e (j x) = P.extL x) (N : Submodule ℂ H) (hN : ∀ x, j x ∈ N) (y : H) : y ∈ N := by
  have h1 : e y ∈ N.map e := by
    have h2 : e y ∈ Submodule.span ℂ (Set.range P.extL) := by
      rw [GlobalTheory.PresBasic.ext_span]
      exact hr.le (LinearMap.mem_range_self _ y)
    refine Submodule.span_le.2 ?_ h2
    rintro _ ⟨x₀, rfl⟩
    exact ⟨j x₀, hN x₀, hj x₀⟩
  obtain ⟨y', hy', h⟩ := h1
  exact hinj h ▸ hy'

theorem coord_translate {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {κ : GA D V} (hκ : κ ∈ GfC V) (a : ℂ)
    {f f' : Bridge.Gf V → c.W} (hf : ∀ h, f' h = a • f (h * (finHom V).rangeRestrict κ)) (ℓ : c.W →ₗ[ℂ] ℂ) (h : GA D V) :
    ℓ (c.ext f' h) = a * ℓ (c.ext f (h * κ)) := by
  have h1 : c.ext f' h = c.ρ h⁻¹ (f' ((finHom V).rangeRestrict h)) := rfl
  have h2 : c.ext f (h * κ) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ))) := rfl
  have h3 : c.ρ (h * κ)⁻¹ = c.ρ h⁻¹ :=
    (congrArg c.ρ (mul_inv_rev h κ)).trans ((c.ρ.map_mul κ⁻¹ h⁻¹).trans
      ((congrArg (· * c.ρ h⁻¹) (hc.1 κ⁻¹ ((GfC V).inv_mem hκ))).trans (one_mul _)))
  have h4 := MonoidHom.map_mul (finHom V).rangeRestrict h κ
  have h5 : f' ((finHom V).rangeRestrict h) = a • f ((finHom V).rangeRestrict (h * κ)) :=
    (hf _).trans (congrArg (fun q => a • f q) h4.symm)
  rw [h1, h2, h3, h5]
  exact (congrArg ℓ ((c.ρ h⁻¹).map_smul a _)).trans (ℓ.map_smul a _)

end Act

end GlobalTheory.SecLift

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjLocal

section Field

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem val_unif : P.valuation E ((Formalism.L2.Host.unif P : Eˣ) : E) = WithZero.exp (-1 : ℤ) := by
  have h := Formalism.L2.Host.unif_spec P
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact h

theorem mk_unit {u : E} (hu : P.valuation E u = 1) : FinitePlace.mk P u = 1 := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, hu]
  simp

theorem mk_unif : FinitePlace.mk P ((Formalism.L2.Host.unif P : Eˣ) : E) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def, val_unif,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp

end Field

variable {D : D7}

noncomputable def locHom {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ where
  toFun := locU he
  map_one' := Units.ext (by rw [locU_val]; simp [locE])
  map_mul' k l := Units.ext (by rw [Units.val_mul, locU_val, locU_val, locU_val, locE_mul_locE he, Units.val_mul])

theorem locE_parts {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (u : D.host.E)
    (hu : P.valuation D.host.E u ≤ 1) : infPart D (locE D e u) = 1 ∧ finPart D (locE D e u) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(GlobalTheory.HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), ?_⟩
  rw [hint]
  intro Q
  have h4 : ι (finPart D (incA D u)) = algebraMap D.host.E _ u := hι u
  have h5 : ι (finPart D (locE D e u)) = 1 + ι (finPart D e) * (ι (finPart D (incA D u)) - 1) :=
    GlobalTheory.HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5, h4]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) u - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q u).trans_le hu
  · rw [h3 Q hQ]
    simp

end GlobalTheory.EtaConjLocal
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.EigenSpanSat

def eigenSub {K : Type} [Field K] {n : ℕ} {O : Type} (r : O → Matrix (Fin n) (Fin n) K)
    (τ : O → K) : Submodule K (Fin n → K) where
  carrier := {c | ∀ a, (r a).mulVec c = τ a • c}
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [Matrix.mulVec_add, hx a, hy a, smul_add]
  zero_mem' := by
    intro a
    simp
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Matrix.mulVec_smul, hx a, smul_comm]

theorem map_mulVec {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    (M.map iK).mulVec (fun i => iK (c i)) = fun i => iK (M.mulVec c i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem eq_zero_of_eigen {K L : Type} [Field K] [Field L] (iK : K →+* L) {n : ℕ} {O : Type}
    (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) {m : ℕ} (σ : Fin m → L)
    (c : Fin m → (Fin n → K))
    (hP : ∀ d : Fin m → K, (∀ a, (r a).mulVec (∑ i, d i • c i) = τ a • ∑ i, d i • c i) →
      ∑ i, d i • c i = 0)
    (he : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (c i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (c i t)) :
    ∑ i, σ i • (fun t => iK (c i t)) = 0 := by
  let _ : Algebra K L := iK.toAlgebra
  let S := Submodule.span K (Set.range σ)
  have : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range σ)
  let b := Module.finBasis K S
  have hli : LinearIndependent K (fun k => (b k : L)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let D : Fin (finrank K S) → Fin m → K :=
    fun k i => b.repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩ k
  have hσ : ∀ i, σ i = ∑ k, iK (D k i) * (b k : L) := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨σ i, Submodule.subset_span ⟨i, rfl⟩⟩)
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Algebra.smul_def]
    rfl

  have hvan : ∀ v : Fin (finrank K S) → (Fin n → K),
      (∑ k, (b k : L) • fun t => iK (v k t)) = 0 → ∀ k, v k = 0 := by
    intro v hv k
    funext t
    have h := congrFun hv t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have := Fintype.linearIndependent_iff.1 hli (fun k => v k t) (by
      rw [← h]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl)
    exact this k
  let u : Fin (finrank K S) → (Fin n → K) := fun k => ∑ i, D k i • c i
  have hy : (∑ i, σ i • (fun t => iK (c i t))) = ∑ k, (b k : L) • fun t => iK (u k t) := by
    funext t

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, u, map_sum, map_mul, hσ,
    Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hu : ∀ k, u k = 0 := by
    intro k
    apply hP
    intro a
    have h1 := hvan (fun k => (r a).mulVec (u k) - τ a • u k) (by
      have h2 := he a
      rw [hy, Matrix.mulVec_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mulVec_smul, map_mulVec, smul_comm (iK (τ a)), ← smul_sub]
      congr 1
      funext t
      simp [map_sub, map_mul])
    exact sub_eq_zero.1 (h1 k)
  rw [hy]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hu k]
  funext t
  simp

end GlobalTheory.EigenSpanSat

namespace GlobalTheory.EigenSpanSat

theorem span_eigen_sat : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (Λ : Submodule (𝓞 K) (Fin n → K)) (O : Type) (r : O → Matrix (Fin n) (Fin n) K) (τ : O → K) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : Formalism.L2.Pj.CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → Λ.FG → ∀ x : Fin n → T.Fr, x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' (Λ : Set (Fin n → K))) → (∀ a, ((r a).map iK).mulVec x = iK (τ a) • x) → x ∈ Submodule.span T.V ((fun (c : Fin n → K) i => iK (c i)) '' {c | c ∈ Λ ∧ ∀ a, (r a).mulVec c = τ a • c}) := by
  intro K _ _ n Λ O r τ 𝔓 T iK _ hFG x hx he
  obtain ⟨C, -, hdec, hCW⟩ :=
    Formalism.L2.Geo.ExtensionFiltration.ExtInvS7cd.exists_compl_inf Λ hFG (eigenSub r τ)
  obtain ⟨m, s, g, hg⟩ := Submodule.mem_span_set'.1 hx
  choose l hl hlg using fun i => (g i).2
  choose p hp q hq hpq using fun i => hdec (l i) (hl i)
  let σ : Fin m → T.Fr := fun i => algebraMap T.V T.Fr (s i)
  have hsplit : x = ∑ i, σ i • (fun t => iK (p i t)) + ∑ i, σ i • (fun t => iK (q i t)) := by
    rw [← hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hlg i, hpq i, ← smul_add, algebraMap_smul]
    congr 1
    funext t
    simp
  have hpE : ∀ i a, (r a).mulVec (p i) = τ a • p i := fun i => (hp i).2
  have hx1 : ∀ a, ((r a).map iK).mulVec (∑ i, σ i • fun t => iK (p i t)) =
      iK (τ a) • ∑ i, σ i • fun t => iK (p i t) := by
    intro a
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, map_mulVec, hpE i a, smul_comm]
    congr 1
    funext t
    simp
  have hx2 : ∑ i, σ i • (fun t => iK (q i t)) = 0 := by
    refine eq_zero_of_eigen iK r τ σ q (fun d hd => ?_) (fun a => ?_)
    · refine hCW _ (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (hq i))) hd
    · have h := he a
      rw [hsplit, Matrix.mulVec_add, hx1 a, smul_add] at h
      exact add_left_cancel h
  rw [hsplit, hx2, add_zero]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p i, ⟨(hp i).1, (hp i).2⟩, rfl⟩)

end GlobalTheory.EigenSpanSat
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem chiDeltaU_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n m : ℕ}
    (q : ℕ) (α : Fin m → ℂ) (b c : GU σ n)
    (h : ∀ i, ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) :
    chiDeltaU q α b = chiDeltaU q α c := by
  unfold chiDeltaU
  simp only [h]

end GlobalTheory.WeylCell.RankOneUnitary

namespace GlobalTheory.WeylCell.RankOneUnitary

theorem ordL_of_v_eq {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x : L) (z : ℤ)
    (hx : Valued.v x = ((Multiplicative.ofAdd z : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) : ordL x = -z := by
  unfold ordL
  have h0 : Valued.v x ≠ 0 := by rw [hx]; exact WithZero.coe_ne_zero
  rw [dite_eq_right h0]
  have : WithZero.unzero h0 = Multiplicative.ofAdd z := by
    apply WithZero.coe_injective; rw [WithZero.coe_unzero, hx]
  rw [this]; rfl

end GlobalTheory.WeylCell.RankOneUnitary

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.exists_const_stabiliserLog_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | exact GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | (intros; apply GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.cocompact_lattice_unit_covolume : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ : Γ, γ • g ∈ K) → ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | exact GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | (intros; apply GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one <;> assumption)
end
