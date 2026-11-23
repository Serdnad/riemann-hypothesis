module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle499
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

noncomputable section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntFrameDiag

theorem integralFrame_transport : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (x : Sp T.V ⟶ Y.X) (x' : Sp T.Fr ⟶ Y.X) (e : spMap (algebraMap T.V T.Fr) ≫ x = x'), Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) → ∀ (G : SAB H (Sp T.V)) (ψ : SABMap G Y.t x) (τ : E →+* ℂ) (ub : Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G)), (∀ i, IsTan (ub i)) → (∀ w : epsOver T.V T.V ⟶ G.G, IsTan w → IsEigV c io G τ w → ∃! a : Fin (Dw.mult τ) → T.V, IsComb ub a w) → ∃ ub' : Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) ∧ ∀ v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e v ∈ GlobalTheory.FlagMod.eigLie c x' τ → ∃ a : Fin (Dw.mult τ) → T.V, ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro x x' e hinj G ψ τ ub hT hS
  choose ub' hub' using fun i => GlobalTheory.T.exists_modelTangent_of_pullback_tangent x G ψ (ub i) (hT i)
  refine ⟨ub', hub', fun v hv => ?_⟩
  obtain ⟨w, hw, hvw⟩ := GlobalTheory.T.exists_pullback_tangent_lift_of_modelTangent x G ψ v
  obtain ⟨a, ha, -⟩ := hS w hw (GlobalTheory.T.isEigenvector_integral_of_tangentPullback_mem T io x x' e hinj G ψ τ w v hvw hv)
  exact ⟨a, GlobalTheory.T.pullbackGroupPointToModelGroup_linearCombination x G ψ ub ub' a w v hub' hvw ha⟩

theorem diag_unit_of_intFr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y' : IntFr Xo c T io) (z : Sp T.V ⟶ X.YY), (X.ptY y'.1 = Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ z) → ∀ (k : X.F.J), ⊤ ≤ z ⁻¹ᵁ X.F.U k → ∀ (hz : ⊤ ≤ (X.pt y'.1 ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), (X.F.ChartFr k (X.pt y'.1 ≫ X.inc) hz Q) → (FrBor t Q y'.1) → ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t (some ⟨σ, i⟩) : T.Fr) := by
  intro E _ _ _ H Dw l Xo c Y X T io
  letI := io.toAlgebra
  intro y' z hz0 k hzk hz Q t hQ ht σ i
  have hφ : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  have hl : X.F.Lies (spMap (algebraMap T.V T.Fr) ≫ z) y'.1 := by
    rw [← show X.ptY y'.1 = spMap (algebraMap T.V T.Fr) ≫ z from hz0]
    exact X.lies_ptY y'.1
  have e : spMap (algebraMap T.V T.Fr) ≫ z ≫ X.π = GlobalTheory.FlagMod.frX y'.1 ≫ Y.j := by
    rw [← Category.assoc]; exact hl.1
  obtain ⟨-, G, t', m1, m2, ⟨ub, hT, -, hS, hU⟩, -⟩ := y'.2
  obtain ⟨ψ, ρ, h1, h2, h3⟩ := GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint Y T io y'.1 (z ≫ X.π) e G t' m1 m2
  have hx : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ (X.F.M k).toMChart.U := X.F.inM hzk rfl
  have hx' : ⊤ ≤ (GlobalTheory.FlagMod.frX y'.1 ≫ Y.j) ⁻¹ᵁ (X.F.M k).toMChart.U :=
    e ▸ GlobalTheory.FlagMod.le_preimage_comp _ hx
  have hinj : Function.Injective (GlobalTheory.FlagMod.tanPull (G := Y.t.G) (algebraMap T.V T.Fr) e) := by
    intro u u' huu
    obtain ⟨cv, rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u
    obtain ⟨cv', rfl⟩ := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx).surjective u'
    rw [GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx', GlobalTheory.FlagMod.tanPull_vec _ _ e hx hx'] at huu
    have := (GlobalTheory.FlagMod.vec (X.F.M k).toMChart _ hx').injective huu
    congr 1
    funext j
    exact hφ (congrFun this j)
  obtain ⟨ub', hl', hsp⟩ := integralFrame_transport T io (z ≫ X.π) _ e hinj G ψ σ (ub σ) (hT σ) (hS σ)
  have hub : ∀ j, GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) e (ub' j) = GlobalTheory.FlagMod.frVec Y y'.1 rfl σ j := by
    intro j
    obtain ⟨u', hu1, hu2⟩ := hU σ j
    exact GlobalTheory.T.frameVector_eq_integralFrameTangent_on_model T io y'.1 (z ≫ X.π) e G t' m1 m2 ψ ρ h1 h2 h3 σ j (ub σ j) u' hu1 hu2 (ub' j) (hl' j)
  have key : ∀ (w : Sp T.Fr ⟶ X.YY) (_ : w = spMap (algebraMap T.V T.Fr) ≫ z) (hzw : ⊤ ≤ w ⁻¹ᵁ X.F.U k),
      X.F.ChartFr k w hzw Q → X.F.ChartFr k (spMap (algebraMap T.V T.Fr) ≫ z) (GlobalTheory.FlagMod.le_preimage_comp _ hzk) Q := by
    rintro _ rfl _ h
    exact h
  have hQ' := key _ ((X.pt_inc _).trans hz0) hz hQ
  exact (X.top.diag_unit (algebraMap T.V T.Fr) hφ z hzk hl e σ ub' hub hsp hQ' ht).2 i

end GlobalTheory.IntFrameDiag
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.DifferentGalois

theorem ord_conjDifferent_and_sum : ∀ (E K : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K] (i : E →+* K) (q : ℕ) (w : HeightOneSpectrum (𝓞 K)), q.Prime → ((q : ℕ) : 𝓞 K) ∈ w.asIdeal → (ord_vw w (conjDifferent i) : ℝ) = (different_vp E q : ℝ) * (vAdd w (q : K) : ℝ) ∧ ∑ p ∈ (discr E).natAbs.primeFactors, (different_vp E p : ℝ) * Real.log p = lrd E := by
  intro E K _ _ _ _ _ i q w hq hm
  refine ⟨?_, ?_⟩
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have h1 := DefectSumCompare.vla_discAt i w
    have h2 := GlobalTheory.FlatLine.vla_span (K := K) (x := ((discr E).natAbs : ℕ)) (Nat.cast_ne_zero.2 hd) w
    have h3 := GlobalTheory.FlatLine.vAdd_natCast (K := K) hq hd hm
    have h5 : ((Module.finrank ℚ E * ord_vw w (conjDifferent i) : ℕ) : ℤ) =
        padicValNat q (discr E).natAbs * vAdd w (q : K) := by
      rw [← h1, ← h3]; exact h2
    have h7 := congrArg (Int.cast : ℤ → ℝ) h5
    simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at h7
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [different_vp]
    push_cast
    field_simp
    linarith
  · have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have h1 := DefectSumCompare.log_discr_eq E
    have h2 : Real.log |((discr E : ℤ) : ℝ)| = Real.log ((discr E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h2, Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization] at h1
    have h3 : ∀ p ∈ (discr E).natAbs.primeFactors, ((different_vp E p : ℚ) : ℝ) * Real.log p =
        ((discr E).natAbs.factorization p * Real.log p) / (Module.finrank ℚ E : ℝ) := by
      intro p hp
      rw [different_vp, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
      push_cast
      rw [Nat.padicValNat_def]
      ring
    rw [Finset.sum_congr rfl h3, ← Finset.sum_div, h1]
    field_simp

end GlobalTheory.DifferentGalois
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem conj_sum_zero (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _))
    (hK : (S.A ((j : ℕ) + 1)).IsKsForm) (τ : ℂ ≃+* ℂ) (hτ : ∀ y, τ (Formalism.L2.Host.embLL0 D y) = Formalism.L2.Host.embLL0 D y)
    (n : ℕ) (c : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (h0 : ∑ k, c k • evW YS v₀ j (g k).val = 0) : ∑ k, τ (c k) • evW YS v₀ j (g k).val = 0 := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let σ : S.Ks → ℂ := fun r => D.what₂.embLL (algebraMap S.Ks D.what₂.LL r)
  have hσ : ∀ r, τ (σ r) = σ r := fun r => by
    have := hτ (S.kKs r)
    simp only [σ, ← S.kKs_spec]
    exact this
  have hg : ∀ k, evW YS v₀ j (g k).val = ∑ a, σ (bK.repr (g k) a) • φ a := fun k => by
    conv_lhs => rw [← bK.sum_repr (g k)]

    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul D.what₂.LL, evW_smul, hbK]
  have hexp : ∀ d : Fin n → ℂ, ∑ k, d k • evW YS v₀ j (g k).val =
      ∑ a, (∑ k, d k * σ (bK.repr (g k) a)) • φ a := fun d => by
    simp only [hg, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hz : ∀ a, ∑ k, c k * σ (bK.repr (g k) a) = 0 := fun a =>
    Fintype.linearIndependent_iff.1 hφ _ ((hexp c).symm.trans h0) a
  rw [hexp]
  refine Finset.sum_eq_zero fun a _ => ?_
  have : ∑ k, τ (c k) * σ (bK.repr (g k) a) = τ (∑ k, c k * σ (bK.repr (g k) a)) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hσ]
  rw [this, hz a, map_zero, zero_smul]

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem exists_algExp {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) (hK : (S.A ((j : ℕ) + 1)).IsKsForm)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) {n : ℕ} (z : Fin n → ℂ) (g : Fin n → NX.FmK S ((j : ℕ) + 1))
    (hz : ∀ l, IsAlgebraic ℚ (z l)) (hx : evK YS v₀ hρ i j b x = ∑ l, z l • evW YS v₀ j (g l).val) :
    ∃ (m : ℕ) (a : Fin m → NX.KB S i b) (g' : Fin m → NX.FmK S ((j : ℕ) + 1)),
      x = ∑ k, a k ⊗ₜ[S.Ks] g' k ∧ ∀ k, IsAlgebraic ℚ (ρ.e i b (a k)) := by
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  have hB : ∀ k, B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  have hxe : x = ∑ k, B.equivFun x k ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) := by
    conv_lhs => rw [← B.sum_equivFun x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hB]
    change (B.equivFun x k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1)) = _
    rw [smul_eq_mul, mul_one]
  refine ⟨m, B.equivFun x, fun k => bK k, hxe, ?_⟩

  have h1 : evK YS v₀ hρ i j b x = ∑ k, ρ.e i b (B.equivFun x k) • φ k := by
    conv_lhs => rw [hxe]
    refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (evK_tmul YS v₀ hρ i j b _ _).trans (congrArg _ (congrArg (evW YS v₀ j) (hbK k)))

  let emb : S.Ks →+* ℂ := D.what₂.embLL.comp (algebraMap S.Ks D.what₂.LL)
  let c : Fin n → Fin m → S.Ks := fun l => bK.equivFun (g l)
  have h2 : ∀ l, evW YS v₀ j (g l).val = ∑ k, emb (c l k) • φ k := fun l => by
    have e : (g l).val = ∑ k, algebraMap S.Ks D.what₂.LL (c l k) • bb k := by
      conv_lhs => rw [← bK.sum_equivFun (g l)]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Submodule.coe_smul, hbK, algebraMap_smul]

    rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [evW_smul]
    rfl
  have h3 : ∑ l, z l • evW YS v₀ j (g l).val = ∑ k, (∑ l, z l * emb (c l k)) • φ k := by
    simp_rw [h2, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h4 : ∀ k, ρ.e i b (B.equivFun x k) = ∑ l, z l * emb (c l k) := by
    have h5 : ∑ k, (ρ.e i b (B.equivFun x k) - ∑ l, z l * emb (c l k)) • φ k = 0 := by
      simp_rw [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hx, h3, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hφ _ h5 k)
  intro k
  rw [h4 k]
  have hemb : ∀ y : S.Ks, IsAlgebraic ℚ (emb y) := fun y =>
    (Algebra.IsAlgebraic.isAlgebraic y).algHom emb.toRatAlgHom
  have hmem : ∀ y : ℂ, y ∈ algebraicClosure ℚ ℂ ↔ IsAlgebraic ℚ y := fun y => mem_algebraicClosure_iff
  refine (hmem _).1 ?_
  refine sum_mem fun l _ => mul_mem ?_ ?_
  · exact (hmem _).2 (hz l)
  · exact (hmem _).2 (hemb _)

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

theorem isAlgebraic_of_pow_eq_one {ζ : ℂ} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : IsAlgebraic ℚ ζ :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) 1, by simp [h]⟩

end GlobalTheory.BigOn.Exp
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem de_chi_eq {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    ∃ σ, (((ρ.B i j b).de.chi x : Circle) : ℂ) = ρ.eO i b (algebraMap (D.ntw.O0 i) (D.ntw.O i)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  refine ⟨σ, ?_⟩
  rw [hρ.delta i j b]
  exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)

end GlobalTheory.BigOn.Exp.TwConj
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

abbrev smallInt (D : D7) : Subring ℂ := ((Formalism.L2.Host.embLL0 D).comp (algebraMap (𝓞 ↥D.LL0) ↥D.LL0)).range

theorem span_mono_subring {M : Type} [AddCommGroup M] [Module ℂ M] {O O' : Subring ℂ} (hO : O ≤ O') (S : Set M) {x : M}
    (hx : x ∈ Submodule.span O S) : x ∈ Submodule.span O' S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul a y _ h => exact Submodule.smul_mem _ (⟨a, hO a.2⟩ : O') h

theorem lat_mono {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m)
    (b : Bool) {O O' : Subring ℂ} (hO : O ≤ O') (h : GA D (Vc D j)) {P : PolF D (Wc D j).rank (Vc D j).rank}
    (hP : P ∈ ρ.lat i j b O h) : P ∈ ρ.lat i j b O' h :=
  ⟨hP.1, span_mono_subring hO _ hP.2⟩

theorem smallInt_le {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} (hρ : ρ.Good) (i : X.Tw)
    (b : Bool) : smallInt D ≤ (ρ.eO i b).range := by
  rintro _ ⟨a, rfl⟩
  exact (hρ.isCoefRing i b).int a

theorem exists_inv_of_root {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (u : FractionRing O) (n : ℕ) (hn : n ≠ 0)
    (hu : u ^ n = 1) : ∃ o : O, algebraMap O (FractionRing O) o = u⁻¹ := by
  have h1 : IsIntegral O (u⁻¹ ^ n) := by rw [inv_pow, hu, inv_one]; exact isIntegral_one
  exact IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) h1)

end GlobalTheory.BigOn.Exp
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffNonvanish

open MvPolynomial

theorem exists_coefFn_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  intro D n lam
  refine ⟨⟨Formalism.L2.Col.extVV D.what₂.LL lam, Formalism.L2.Col.extVV_mem D.what₂.LL lam⟩, ?_⟩
  by_contra h
  push_neg at h
  have hmap : MvPolynomial.map D.what₂.embLL (Formalism.L2.Col.extVV D.what₂.LL lam) = 0 := by
    refine GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam _ ?_
    intro x
    have hx := h x
    simp only [coefFn] at hx ⊢
    rw [eval₂Hom_map_hom] at *
    simpa using hx
  exact Formalism.L2.Col.extVV_ne_zero D.what₂.LL lam
    ((map_eq_zero_iff _ (MvPolynomial.map_injective _ D.what₂.embLL.injective)).mp hmap)

end GlobalTheory.CoeffNonvanish
end
end
