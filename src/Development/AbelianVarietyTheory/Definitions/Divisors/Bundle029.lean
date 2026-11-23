module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColRows

open Module NumberField
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef _root_.Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds
open Formalism.LatticeIndexTer (ph)

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def IsFrames (Df : DefSide Bs) (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ) : Prop :=
  ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding

def RowsBody (Dc : DefCols Df) (u : Dc.Mem) (Q : KerChain K) (f0 : (Fin (Dc.a u) → K) →ₗ[K] (Q.F 0).Forms)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums Bs.J Pl) : Prop :=
  ∃ (ch : ColChain Dc u) (T : ChainTie ch Q), T.First (f0.comp (LinearMap.funLeft K K (Fin.cast ch.c0.symm))) ∧
    ∃ (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
      (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
      (hn : HtNums R (InfinitePlace K))
      (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
        (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn)
      (cb : CBData ch.X ch.Kj),
      ∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v

def FamFramed (F : GFam K) (h : F.Ok) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] F.Forms) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
    ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = famIpAt F h v (e x) (e x)

def DatFramed (S : GSD K) (h : S.Ok) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → K) ≃ₗ[K] S.EqFun) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) ∧
    ∀ v x, ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x ^ 2 : ℝ) : ℂ) = S.ipAt h v (e x) (e x)

def FactorBounds (Q : KerChain K) {J : Type} [Fintype J] (no : J → ℕ) (t : J → InfinitePlace K → ℝ) : Prop :=
  (∀ i < Q.n, ∀ v, StepBound_sq Q i v (∑ l ∈ Finset.univ.filter (fun l => no l = i), t l v)) ∧
    ∀ v, CplBound_sq Q v (∑ l ∈ Finset.univ.filter (fun l => Q.n ≤ no l), t l v)

end Generic

section Numbers

variable {J Pl : Type} [Fintype J] [Fintype Pl] [DecidableEq Pl] (R : RecNums J Pl)

def KerSide (Emb : Type) [Fintype Emb] (C : ℝ) (P : (J → Emb → ℝ) → Prop) : Prop :=
  ∃ (g0 : J → ℝ) (MainNotions : J → Emb → ℝ) (logOm : Pl → Emb → ℝ) (logth0 : Emb → ℝ) (logh logh' : J → ℝ) (vv logg : ℝ),
    (∀ τ, (∑ s, logOm τ s) / (Fintype.card Emb : ℝ) = R.logOm) ∧
    (∀ j s, MainNotions j s ≤ C * R.f * R.m ^ 2 * R.Nn ^ 2 * (logg + R.logT) + C * R.f * R.Nn ^ 2 * logg) ∧
    (∑ s, logth0 s) / (Fintype.card Emb : ℝ) ≤ C * R.L ∧
    (∀ j, logh j ≤ C * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)) ∧
    (∀ j, logh' j ≤ C * R.f * R.Nn ^ 2 * (R.L + R.logT + logg)) ∧
    (∀ j, 0 ≤ g0 j ∧ g0 j ≤ R.Nn ^ 2) ∧
    (∀ j, Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * vv) ≤ C * R.La) ∧
    (∀ j τ, Real.log (2 * (∑ i, R.ν j τ i) + 2) ≤ C * R.La) ∧ logg ≤ C * R.L ∧
    P (Formalism.DimensionVariation.liftedMapLogSize R.ν g0 MainNotions logOm logth0 logh logh' vv)

def LastSide (CT A : ℝ) : Prop :=
  ∃ bT nτ lam1 D0 D1 logc logxi : Pl → ℝ,
    A ≤ -(∑ τ, nτ τ * R.logT) + (∑ τ, (2 * logc τ + logxi τ)) ∧
    (∀ τ, logc τ ≤ (R.Nn - 1) * D1 τ * Real.log (2 * R.a)) ∧
    (∀ τ, logxi τ ≤ R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)) ∧
    (∀ τ, nτ τ = lam1 τ - D0 τ) ∧ (∀ τ ∈ R.TT, lam1 τ = R.aT τ - (R.Nn - R.k) / 2) ∧
    (∀ τ, τ ∉ R.TT → R.S - (R.Nn - 1) / 2 ≤ lam1 τ) ∧
    (∀ τ, D0 τ ≤ R.S + R.m * R.η + (if τ ∈ R.TT then bT τ else 0)) ∧
    (∀ τ, D1 τ ≤ 3 * D0 τ + R.S + R.η) ∧ (∀ τ ∈ R.TT, bT τ ≤ 2 * R.b') ∧
    0 ≤ R.logT ∧ R.logT ≤ CT * R.m * R.L

end Numbers

structure Reads (N : NumDatum) {J : Type} [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ) (R : RecNums J (RPl N.R)) : Prop where
  tops : ∀ z, z ∈ R.TT ↔ IsTopPl N z
  aT : ∀ t ∈ N.TT, R.aT (false, t) = ((N.aT t : ℚ) : ℝ)
  logT : R.logT = Real.log (T : ℝ)
  phNu : ∀ j z, ∑ i, ph (R.ν j z i) = ∑ i ∈ Finset.range (N.R.N (eJ j).1), ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)
  sumNu : ∀ j z, ∑ i, R.ν j z i = ((N.nuAbs δ ((eJ j).1 + 1) z : ℚ) : ℝ)
  nums : R.L = N.sc.L ∧ R.a = N.sc.a ∧ R.b = N.sc.b ∧ R.La = N.La ∧ R.m = N.R.m ∧ R.f = N.R.f ∧ R.k = N.R.k ∧ R.Nn = N.Nm ∧
    R.S = N.Sc ∧ R.η = N.eta ∧ R.b' = N.sc.b' ∧ R.logOm = N.logOm

def lastLog {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) : ℝ :=
  -((∑ τ, Br.nBr (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
    Real.log (∏ τ, ((Br.cBr (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℝ) ^ 2 *
      Br.kapBr ℝ (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ))

end GlobalTheory.ColRows
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.DI

def IsLifted (p : ℕ) {X : Scheme.{0}} [IsIntegral X] (Z : Set X) {ι : Type} (U : ι → X.Opens) {n : ℕ}
    (x : ι → Fin n → X.functionFieldˣ) : Prop :=
  ∃ (Kt : Type) (_ : CommRing Kt) (π : Kt →+* X.functionField) (F : ι → Kt →+* Kt),
    IsFlatLift p π ∧ (∀ i, IsFrob p π (F i)) ∧
    (∀ i l, ∃ z, π z = (x i l : X.functionField) ∧ F i z = z ^ p) ∧
    ∀ (y : X) (s : Finset ι), (∀ i ∈ s, y ∈ U i) → ∀ g : X.functionFieldˣ, LogDR.LogUnit Z y g →
      LogLift p π F s (LogDR.locRing y : Set X.functionField) (g : X.functionField)

def stalkIm {Y : Scheme.{0}} {η y : Y} (h : η ⤳ y) : Subring (Y.presheaf.stalk η) :=
  (Y.presheaf.stalkSpecializes h).hom.range

end GlobalTheory.DI
end
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

end GlobalTheory.LevPullModel
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC pullbackSections)
open GlobalTheory.DualPull (adj adj_app pull_ext appLE_resG resG_appLE theta toCut ofCut cutEquiv)
open GlobalTheory.VB GlobalTheory.Conormal

namespace GlobalTheory.LieVB

section Eigen

variable {X Y : Scheme.{0}} {F G : X.Modules} {O : Type} [CommRing O] {ρ : O →+* End F}
  {ρ' : O →+* End G} (σ : O →+* Γ(X, ⊤))

theorem isEquivariant_inv {φ : F ≅ G} (h : IsEquivariant ρ ρ' φ.hom) :
    IsEquivariant ρ' ρ φ.inv := fun a => by
  rw [Iso.comp_inv_eq, Category.assoc, h a, Iso.inv_hom_id_assoc]

variable (ρ)

theorem smul_eq_smulHom_comp (a : Γ(X, ⊤)) (φ : F ⟶ G) : a • φ = smulHom F a ≫ φ :=
  (smul_hom_def a φ).trans (smulHom_comp a φ).symm

theorem dualMap_smul (a : Γ(X, ⊤)) (φ : F ⟶ G) : dualMap (a • φ) = a • dualMap φ := by
  rw [smul_eq_smulHom_comp, dualMap_comp, dualMap_smulHom]
  rfl

def dualQuotHom : dual (eigenQuot ρ σ) ⟶ eigen (dualAct ρ) σ :=
  eigenLift (ρ := dualAct ρ) (σ := σ) (dualMap (eigenπ ρ σ)) fun a => by
    rw [act_dualAct, ← dualMap_comp, act_eigenπ, dualMap_smul]

instance isIso_dualQuotHom : IsIso (dualQuotHom ρ σ) := by
  refine Twist.isIso_of_bijective _ fun V => ⟨Function.Injective.of_comp
    (f := (eigenι (dualAct ρ) σ).app V) (QCoh.injective_app_of_mono (dualMap (eigenπ ρ σ)) V),
    fun s => ?_⟩
  let l := (eigenι (dualAct ρ) σ).app V s
  have hl (a : O) : act ρ a ≫ toCut l = σ a • toCut l := by
    ext W t
    apply (cutEquiv V W).injective
    have := congrArg (fun m => dualApp m (DualPull.cutO_le' V W) (resM F (DualPull.cutO_le V W) t))
      (mem_eigenSub_iff.1 ((eigenSub (dualAct ρ) σ).incl_app_mem s) a)
    refine ((DualPull.toCut_app l W _).trans ?_).trans (DualPull.cutEquiv_smul V W _ _).symm
    refine (congrArg _ (app_resM (act ρ a) _ t).symm).trans (this.trans ?_)
    rw [dualApp_smul, resG_resG]
    exact congrArg₂ (fun x y : Γ(X, DualPull.cutO V W) => x * y) (resG_resG _ _ _).symm rfl
  refine ⟨ofCut (eigenDesc _ hl), (eigenSub (dualAct ρ) σ).incl_app_injective V
    (dual_ext fun W h t => ?_)⟩
  refine (DualPull.dualApp_ofCut _ h ((eigenπ ρ σ).app W t)).trans ?_
  rw [show (eigenDesc _ hl).app W ((eigenπ ρ σ).app W t) = (toCut l).app W t from
    congr(($(eigenπ_desc ρ σ _ hl)).app W t), DualPull.toCut_app, ← dualApp_resM, resM_resM,
    resM_self]
  rfl

def dualQuotIso : dual (eigenQuot ρ σ) ≅ eigen (dualAct ρ) σ := asIso (dualQuotHom ρ σ)

theorem dualQuotIso_hom_ι :
    (dualQuotIso ρ σ).hom ≫ eigenι _ _ =
      dualMap (eigenπ ρ σ) := by
  simp only [dualQuotIso, asIso_hom, dualQuotHom, eigenLift_ι]

def pullbackQuotIso (f : Y ⟶ X) : eigenQuot (pullAct ρ f) (f.appTop.hom.comp σ) ≅
    (Scheme.Modules.pullback f).obj (eigenQuot ρ σ) where
  hom := eigenDesc ((Scheme.Modules.pullback f).map (eigenπ ρ σ)) fun a => by
    rw [act_pullAct, ← Functor.map_comp, act_eigenπ, pullback_map_smul]; rfl
  inv := adj f (eigenDesc ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (eigenπ (pullAct ρ f) (f.appTop.hom.comp σ))) fun a => by
      rw [← Adjunction.homEquiv_naturality_left, smul_eq_smulHom_comp,
        ← Adjunction.homEquiv_naturality_left, pullback_map_smulHom, ← smul_eq_smulHom_comp]
      exact congrArg _ (act_eigenπ (pullAct ρ f) _ a))
  hom_inv_id := by
    rw [← cancel_epi (eigenπ _ _), eigenπ_desc_assoc, Category.comp_id, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [← cancel_epi ((Scheme.Modules.pullback f).map (eigenπ ρ σ)), ← Category.assoc, adj,
      ← Adjunction.homEquiv_naturality_left_symm, eigenπ_desc, Equiv.symm_apply_apply, eigenπ_desc,
      Category.comp_id]

theorem hom_ext_of_isFrame {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)} (he : IsFrame e)
    {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (app_resM φ _ _).trans ((congrArg _ (h i)).trans (app_resM ψ _ _).symm)

end Eigen

theorem isFrame_d_Spec {R A : CommRingCat.{0}} [Algebra R A] (ε : A →ₐ[R] R)
    {π : Spec A ⟶ Spec R} {e : Spec R ⟶ Spec A} (he : e ≫ π = 𝟙 _)
    (hπ : π = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hε : e = Spec.map (CommRingCat.ofHom ε.toRingHom)) {κ : Type} [Fintype κ]
    (b : Module.Basis κ R (AugCot ε)) (a : κ → A) (hb : ∀ i, b i = AugCot.d ε (a i)) :
    IsFrame fun i => d he (W := ⊤) (V := ⊤) le_top ((Scheme.ΓSpecIso A).inv (a i)) := by
  subst hπ hε
  exact IsChart.isFrame_d he ⟨isAffineOpen_top _, isAffineOpen_top _, le_top, le_top⟩ ε
    (Scheme.ΓSpecIso R).inv.hom (Scheme.ΓSpecIso A).inv.hom
    (IsPushout.of_vert_isIso (g := (Scheme.ΓSpecIso R).inv) (inl := (Scheme.ΓSpecIso A).inv)
      ⟨Scheme.ΓSpecIso_inv_naturality _⟩)
    (fun x => congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ε.toRingHom)) x).symm)
    b a hb

end GlobalTheory.LieVB
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

def IsGal {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} (π : W ⟶ Z) (hπ : π ≫ s = sW) (G : Type) [Group G]
    (act : G → (W ⟶ W)) : Prop :=
  GlobalTheory.ZM.IsGaloisCover G (fun g => act g⁻¹) π

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

theorem mk' (hG : Finite G) (hfin : IsFinite π) (het : Etale π) (hon : Surjective π) (hinv : ∀ g, act g ≫ π = π)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) (hone : act 1 = 𝟙 W)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W), a ≫ π = b ≫ π → ∃! g : G, b = a ≫ act g) :
    IsGal π hπ G act := by
  refine GlobalTheory.ZM.IsGaloisCover.mk hG ?_ ?_ (fun a => hinv a⁻¹) hfin het hon ?_
  · simpa only [inv_one] using hone
  · intro a c
    simpa only [mul_inv_rev] using hmul c⁻¹ a⁻¹
  · intro K _ _ y y' e
    obtain ⟨g, hg, hu⟩ := hfib K y y' e
    refine ⟨g⁻¹, by simpa only [inv_inv] using hg.symm, fun a ha => ?_⟩
    simpa only [inv_inv] using congrArg Inv.inv (hu a⁻¹ ha.symm)

theorem finite (h : IsGal π hπ G act) : Finite G := GlobalTheory.ZM.IsGaloisCover.finite h
theorem etale (h : IsGal π hπ G act) : Etale π := GlobalTheory.ZM.IsGaloisCover.etale h
theorem surjective (h : IsGal π hπ G act) : Surjective π := GlobalTheory.ZM.IsGaloisCover.onto h

theorem act_comp (h : IsGal π hπ G act) (g : G) : act g ≫ π = π := by
  simpa using GlobalTheory.ZM.IsGaloisCover.inv h g⁻¹

theorem fibre (h : IsGal π hπ G act) (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W) :
    a ≫ π = b ≫ π ↔ ∃! g : G, b = a ≫ act g := by
  constructor
  · intro e
    obtain ⟨g, hg, hu⟩ := GlobalTheory.ZM.IsGaloisCover.fibre h K a b e
    refine ⟨g⁻¹, hg.symm, fun g' hg' => ?_⟩
    have := hu g'⁻¹ (by simpa using hg'.symm)
    simp [← this]
  · rintro ⟨g, hg, -⟩
    rw [hg, Category.assoc, h.act_comp]

end IsGal

end GlobalTheory.W1
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

variable {S : Scheme.{0}} (A : Over S)

def Same {T U Y : Over S} (N : LB (A ⊗ T).left) (M : LB (A ⊗ U).left) (y : Y ⟶ T) (u : Y ⟶ U) : Prop :=
  LBIso (ev N (fst A Y) (snd A Y ≫ y)) (ev M (fst A Y) (snd A Y ≫ u))

def Inj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (Y : Over S) (u u' : Y ⟶ U), Same A M M u u' → u = u'

def FibInj {U : Over S} (M : LB (A ⊗ U).left) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (Y : Over S) (_ : Y ⟶ Over.mk s) (u u' : Y ⟶ U),
    Same A M M u u' → u = u'

def ChartAt {U T : Over S} (M : LB (A ⊗ U).left) (N : LB (A ⊗ T).left) : Prop :=
  ∃ W : T.left.Opens, ∀ (Y : Over S) (y : Y ⟶ T), (∃ u : Y ⟶ U, Same A N M y u) ↔ ∀ z, y.left z ∈ W

structure Good (g : ℕ) {X Y : Scheme.{0}} (f : X ⟶ Y) : Prop where
  proper : IsProper f
  smooth : SmoothOfRelativeDimension g f
  conn : GeometricallyConnected f

def FinAff (X : Scheme.{0}) : Prop :=
  ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

def DimLe (B : Over S) : Prop :=
  ∀ (g : ℕ) (T : Scheme.{0}) (t : T ⟶ S),
    SmoothOfRelativeDimension g (pullback.snd A.hom t) → SmoothOfRelativeDimension g (pullback.snd B.hom t)

variable [GrpObj A]

structure Fam {T : Over S} (N : LB (A ⊗ T).left) : Prop where
  isLB : N.IsLB
  add : IsAdditive N

structure IsChart {U : Over S} (M : LB (A ⊗ U).left) : Prop where
  fam : Fam A M
  inj : Inj A M
  chart : ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N

structure Rep {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) : Prop where
  fam : Fam A P
  univ : ∀ (T : Over S) (t : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N →
    ∃! x : T ⟶ B, x ≫ b = t ∧ LBIso N (ev P (fst A T) (snd A T ≫ x))

def HasRep (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left

def HasRepAF (g : ℕ) (S' : Over S) : Prop :=
  ∃ (B : Over S) (b : B ⟶ S') (P : LB (A ⊗ B).left), Rep A b P ∧ Good g b.left ∧ FinAff B.left

def LiftAt (g : ℕ) {B S' : Over S} (b : B ⟶ S') (P : LB (A ⊗ B).left) (x : B.left) : Prop :=
  ∃ (U : Over S) (M : LB (A ⊗ U).left) (j : U ⊗ S' ⟶ B), Fam A M ∧ SmoothOfRelativeDimension g U.hom ∧
    j ≫ b = snd U S' ∧ IsOpenImmersion j.left ∧ x ∈ Set.range j.left ∧ Same A M P (fst U S') j

variable {A}


omit [GrpObj A] in
theorem same_id_iff {T U : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (u : T ⟶ U) : Same A N M (𝟙 T) u ↔ LBIso N (ev M (fst A T) (snd A T ≫ u)) := by
  rw [Same, ← cls_eq_iff (pull_isLB hN _) (pull_isLB hM _), ← cls_eq_iff hN (pull_isLB hM _), cls_ev hN, evc,
    Category.comp_id, lift_fst_snd, Over.id_left, pull_id]


omit [GrpObj A] in
theorem same_iff {T U Y : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    (y : Y ⟶ T) (u : Y ⟶ U) :
    Same A N M y u ↔ evc hN (fst A Y) (snd A Y ≫ y) = evc hM (fst A Y) (snd A Y ≫ u) :=
  (cls_eq_iff (pull_isLB hN _) (pull_isLB hM _)).symm

end GlobalTheory.DualCon
end
end
