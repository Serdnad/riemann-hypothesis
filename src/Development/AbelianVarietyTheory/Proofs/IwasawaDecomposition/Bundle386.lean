module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle094
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import Formalism.MoebiusJetDuality.StatementU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HodgeDomain.ActionDeriv

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  have h : ∀ᶠ x in nhds x0, ∀ τ, (1 - (unflat x τ)ᴴ * unflat x τ).PosDef := by
    refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually _ (fun a b => ?_)
      (fun x => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
    fun_prop
  exact h

theorem diffOn_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s) :
    ContDiffOn ℂ 1 (fun z => (M z).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem diffOn_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set V} {n : ℕ}
    {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiffOn ℂ 1 (fun z => M z a b) s)
    (hd : ∀ z ∈ s, (M z).det ≠ 0) (a b : Fin n) : ContDiffOn ℂ 1 (fun z => (M z)⁻¹ a b) s := by
  have hadj : ContDiffOn ℂ 1 (fun z => (M z).adjugate a b) s := by
    simp only [adjugate_apply]
    refine diffOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (diffOn_det h) hd) hadj

theorem diffOn_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) :
    DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) := by
  refine differentiableOn_pi.2 fun x => ?_
  obtain ⟨τ, a, b⟩ := x
  refine ContDiffOn.differentiableOn (n := 1) ?_ one_ne_zero
  have hinv : ∀ k, ContDiffOn ℂ 1 (fun v => (kapQ (g τ) (unflat v τ))⁻¹ k b) (DomFlat ι p q) := by
    intro k
    refine diffOn_inv (s := DomFlat ι p q) (M := fun v => kapQ (g τ) (unflat v τ)) (fun i j => ?_) (fun v hv => (kapQ_isUnit (hg τ (Set.mem_univ _)) (hv τ)).ne_zero) k b
    simp only [kapQ, Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
    fun_prop
  simp only [flat, moebI, moeb, Matrix.mul_apply]
  refine ContDiffOn.sum fun k _ => ContDiffOn.mul ?_ (hinv k)
  simp only [Matrix.add_apply, Matrix.mul_apply, unflat, Matrix.of_apply]
  fun_prop

theorem hasDerivAt_affine {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin m) (Fin k) ℂ)
    (z ξ : Matrix (Fin n) (Fin k) ℂ) (a : Fin m) (b : Fin k) :
    HasDerivAt (fun t : ℂ => (A * (z + t • ξ) + B) a b) ((A * ξ) a b) 0 := by
  have e : (fun t : ℂ => (A * (z + t • ξ) + B) a b) = fun t => t * (A * ξ) a b + (A * z + B) a b := by
    funext t
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((A * ξ) a b)).add_const ((A * z + B) a b)

theorem fderiv_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) :
    fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) =
      flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) := by
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hn := isOpen_domFlat.mem_nhds hz'
  have hF := ((diffOn_moebI hg).differentiableAt hn).hasFDerivAt
  set D := fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) with hD
  have hc : HasDerivAt (fun t : ℂ => flat z + t • flat ξ) (flat ξ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (flat ξ)).const_add (flat z)
  have hW : HasDerivAt (fun t : ℂ => flat (moebI g (unflat (flat z + t • flat ξ)))) D 0 :=
    hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  have hev : ∀ᶠ t : ℂ in nhds 0, flat z + t • flat ξ ∈ DomFlat ι p q :=
    hc.continuousAt.eventually_mem (by simpa using hn)
  funext x
  obtain ⟨τ, a, b⟩ := x
  have hgτ := hg τ (Set.mem_univ _)
  have key : unflat D τ * kapQ (g τ) (z τ) = jW (g τ) (z τ) * ξ τ := by
    rw [jW, Matrix.sub_mul, eq_sub_iff_add_eq, Matrix.mul_assoc]
    ext i j
    have h1 := hasDerivAt_affine (g τ).1.toBlocks₁₁ (g τ).1.toBlocks₁₂ (z τ) (ξ τ) i j
    have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_pi.1 hW (τ, i, k)).mul (hasDerivAt_affine (g τ).1.toBlocks₂₁ (g τ).1.toBlocks₂₂ (z τ) (ξ τ) k j)
    have h3 := h2.congr_of_eventuallyEq (f₁ := fun t : ℂ =>
      ((g τ).1.toBlocks₁₁ * (z τ + t • ξ τ) + (g τ).1.toBlocks₁₂) i j) (by
        filter_upwards [hev] with t ht
        have := moeb_mul_kapQ hgτ (ht τ)
        exact (congrFun (congrFun this i) j).symm)
    rw [h1.unique h3, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
    simp only [zero_smul, add_zero]
    rfl
  have e : unflat D τ = tanAct (g τ) (z τ) (ξ τ) := by
    rw [tanAct, ← key, mul_nonsing_inv_cancel_right _ _ (kapQ_isUnit hgτ (hz τ))]
  exact congrFun (congrFun e a) b

theorem isOpen_and_fderiv_moebI : ∀ (ι : Type) [Fintype ι] (p q : ℕ), IsOpen (DomFlat ι p q) ∧ ∀ g ∈ UpqI ι p q, DifferentiableOn ℂ (fun v => flat (moebI g (unflat v))) (DomFlat ι p q) ∧ ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, fderiv ℂ (fun v => flat (moebI g (unflat v))) (flat z) (flat ξ) = flat (fun τ => tanAct (g τ) (z τ) (ξ τ)) :=
  fun _ _ _ _ => ⟨isOpen_domFlat, fun _ hg => ⟨diffOn_moebI hg, fun _ hz ξ => fderiv_moebI hg hz ξ⟩⟩

end GlobalTheory.HodgeDomain.ActionDeriv
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocFrame

section Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
open GlobalTheory.LieMet (tanOf isTan_tv isTan_map tan_ext)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T U : Type} [CommRing S] [CommRing T] [CommRing U] {x : Sp S ⟶ X} {x' : Sp T ⟶ X} {x'' : Sp U ⟶ X}

def res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (v : TanM x t.G) : TanM x' t.G := tanOf (isTan_map ψ hx (isTan_tv v))

theorem res_res (ψ : S →+* T) (hx : spMap ψ ≫ x = x') (χ : T →+* U) (hx' : spMap χ ≫ x' = x'') {ω : S →+* U}
    (e : χ.comp ψ = ω) (hx'' : spMap ω ≫ x = x'') (v : TanM x t.G) :
    res χ hx' (res ψ hx v) = res ω hx'' v := by
  subst e
  refine tan_ext ?_
  show spMap (Formalism.L2.Pj.dualMap χ) ≫ spMap (Formalism.L2.Pj.dualMap ψ) ≫ _ = spMap (Formalism.L2.Pj.dualMap (χ.comp ψ)) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  congr 2
  exact RingHom.ext fun a => by ext <;> simp [Formalism.L2.Pj.dualMap]

theorem res_sum (ψ : S →+* T) (hx : spMap ψ ≫ x = x') {κ : Type} [Fintype κ] (a : κ → S) (n : κ → TanM x t.G) :
    res ψ hx (∑ k, a k • n k) = ∑ k, ψ (a k) • res ψ hx (n k) := by
  subst hx
  have dual_alg : (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp ψ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have eps_dual (b : S) : spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (epsMul b) =
      spMap (epsMul (ψ b)) ≫ spMap (Formalism.L2.Pj.dualMap ψ) := by
    rw [spMap_comp_spMap, spMap_comp_spMap]
    congr 1
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, epsMul, mul_comm]
  let ρ : overAt (spMap ψ ≫ x) (DualNumber T) ⟶ overAt x (DualNumber S) := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dual_alg])
  let f : TanM x t.G →+ TanM (spMap ψ ≫ x) t.G :=
    AddMonoidHom.mk' (res ψ rfl) fun a b => by
      apply tan_ext
      have h := congrArg (fun f => f.left) (MonObj.comp_mul ρ (tv a) (tv b))
      rw [tv_add]
      exact h
  refine (map_sum f _ _).trans (Finset.sum_congr rfl fun k _ => tan_ext ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (tv (n k)).left) (eps_dual (a k))).trans
    (Category.assoc _ _ _))


end Alg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx
open GlobalTheory.AllWt (Psi)
attribute [local instance] Over.cartesianMonoidalCategory

end GlobalTheory.LieLocFrame
end
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.StepZero

section Gen
open _root_.Formalism.L2.Forms
variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem mem_formsK (S : GStep E K n) (hS : S.Free) (hF : (S.fam emb lam).Ok) (x : S.Cl → VV K lam) : x ∈ S.FormsK emb lam hF := by
  intro c γ
  have hγ : (γ : S.G c.1) = 1 := hS c.1 γ (S.rp c.1 c.2) γ.2
  show (S.rho emb lam c.1) (γ : S.G c.1) (x c) = x c
  rw [hγ, map_one]
  rfl

theorem forms_equiv (S S' : GStep E K n) (hS : S.Free) (hS' : S'.Free) (hF : (S.fam emb lam).Ok) (hF' : (S'.fam emb lam).Ok)
    (e0 : S.Cl ≃ S'.Cl) (hL : ∀ c, S'.Lsh _ (S'.rep (e0 c)) = S.Lsh _ (S.rep c)) :
    ∃ e : (S.hlat emb lam hF).V ≃ₗ[K] (S'.hlat emb lam hF').V,
      (∀ x, x ∈ (S.hlat emb lam hF).L ↔ e x ∈ (S'.hlat emb lam hF').L) ∧
        ∀ x, S'.embF emb σ lam hF' (e x) = fun c => S.embF emb σ lam hF x (e0.symm c) := by
  let f : S.FormsK emb lam hF →ₗ[K] S'.FormsK emb lam hF' :=
    { toFun := fun x => ⟨fun c => x.1 (e0.symm c), mem_formsK emb lam S' hS' hF' _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g : S'.FormsK emb lam hF' →ₗ[K] S.FormsK emb lam hF :=
    { toFun := fun y => ⟨fun c => y.1 (e0 c), mem_formsK emb lam S hS hF _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, ?_, ?_⟩
  · ext y c
    simp [f, g]
  · ext x c
    simp [f, g]
  · intro x
    constructor
    · intro hx c
      have h1 := hx (e0.symm c)
      have h2 := hL (e0.symm c)
      rw [Equiv.apply_symm_apply] at h2
      show x.1 (e0.symm c) ∈ delAtr emb lam (S'.Lsh c.1 (S'.rep c))
      rw [h2]
      exact h1
    · intro hx c
      have h1 : x.1 (e0.symm (e0 c)) ∈ delAtr emb lam (S'.Lsh (e0 c).1 (S'.rep (e0 c))) := hx (e0 c)
      rw [hL c, Equiv.symm_apply_apply] at h1
      exact h1
  · intro x
    rfl
end Gen

attribute [local instance] GlobalTheory.Mem.Col2.starE



theorem law0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ l : I.Laws, I.Law0 l := by
  intro B X I hI l u a
  obtain ⟨e, he1, he2⟩ := forms_equiv B.fields.emb B.embLL (lamT (B.hcW u) 0) (I.stp u I.mu0 0) (I.stp u a 0)
    (l.lev u I.mu0).free0 (l.lev u a).free0 ((l.fmL u I.mu0).fam 0) ((l.fmL u a).fam 0) (I.eCls0 l u a)
    (fun c => by
      have h := (GlobalTheory.T.cl0_bijective_and_deco_eq I hI u a (l.idx0 a).some).2 c
      show ((I.stp u a 0).rep (I.cl0 u a (l.idx0 a).some c)).1.1.deco.1.Lsh = ((I.stp u I.mu0 0).rep c).1.1.deco.1.Lsh
      rw [h])
  exact ⟨e, he1, fun x => he2 x⟩

end GlobalTheory.Mem.Col2.StepZero

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPrimes_away_level_and_type_primes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → (I.Q I.mu0 = ∅) ∧ ∀ (u : B.Word) (a : I.ι), ∀ P ∈ I.Q a, (P ∉ (B.primes X).vT u ∧ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ (B.primes X).vT u ∧ conjPrime₂ P ∉ (B.primes X).vGs ∧ conjPrime₂ P ∉ I.Q a) ∧ X.piT u ∉ P.asIdeal ∧ (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | exact GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away | (intros; apply GlobalTheory.Mem.Col2.TwistPrimes.twist_primes_away <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) :
    Nonempty (I.stp u I.mu0 (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok I.mu0
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u I.mu0 (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u I.mu0 (B.R.m - 1)).cl b0 q0⟩



theorem GlobalTheory.Mem.Col2.TC.levJ_herm_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → 1 ≤ B.R.m - 1 → ∃ H0 : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f, F.levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) H0.Lb ∧ ∀ v, F.levJ.Uloc v = (H0.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← F.levJ_Lb h1 (chOf0 (B.R.m - 1) c0)]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hE := GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (rankN (I.rec7 l Z) (B.R.m - 1) hi)
    (I.rec7 l Z).host.g _ _ rfl F.levJ ?_ ?_ ?_
  · obtain ⟨L, e1, e2, -⟩ := hE
    exact ⟨L, e1, e2⟩
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ F.levJ F.gl F.glevJ a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianStepLevel_of_chartFormsLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  first | exact @GlobalTheory.Mem.Col2.TC.level_of_chart | exact GlobalTheory.Mem.Col2.TC.level_of_chart | (intros; apply GlobalTheory.Mem.Col2.TC.level_of_chart <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_unitary_diagonal_basePoint_levelPrime : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  first | exact @GlobalTheory.Mem.Col2.BasePoint.exists_kStd | exact GlobalTheory.Mem.Col2.BasePoint.exists_kStd | (intros; apply GlobalTheory.Mem.Col2.BasePoint.exists_kStd <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevJRed

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {gp : Fin 2 → ℕ}

theorem mat_one (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) : G.mat j v h fr 1 = 1 := by
  unfold GLoc.mat
  rw [map_one, mul_one, inv_mul_cancel, Units.val_one]

theorem mat_mul (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    G.mat j v h fr (x * y) = G.mat j v h fr x * G.mat j v h fr y := by
  unfold GLoc.mat
  rw [map_mul, ← Units.val_mul]
  congr 1
  group

theorem mat_int (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {J : Matrix (Fin n) (Fin n) E} {Lb : Submodule (𝓞 E) (Fin n → E)} (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : ∀ x : Fin n → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ b, G.phi j v h (y b) = x b) ↔
        ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
          v.adicCompletionIntegers F)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Lb) (a b : Fin n) :
    G.mat j v h fr x a b ∈ v.adicCompletionIntegers F := by
  classical
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1 with hw
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w = Pi.single b 1 := by
    rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (hfr w).2 fun c => by
    rw [hinv]
    by_cases e : c = b
    · subst e
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne e]
      exact zero_mem _
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := hx.2
  have hxy : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hst y).1 hy
  have hphi : ∀ c, G.phi j v h (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) c) =
      (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).map (G.phi j v h)) *ᵥ w) c := by
    intro c

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hyw]
  have key := (hfr _).1 ⟨_, hxy, hphi⟩ a
  convert key using 1
  unfold GLoc.mat
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mulVec_single_one]
  rfl

end Gen

theorem redM_levJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) 1) = 1 ∧ ∀ x ∈ F.levJ.Uloc v, ∀ y ∈ F.levJ.Uloc v, redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) (x * y)) = redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) * redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) y) := by
  intro B X I _ _ l Z u Ch0 chOf0 F _ j v hv
  have hint : ∀ x ∈ F.levJ.Uloc v, ∀ a b, F.gl.mat j v hv (F.glevJ.fr j v hv) x a b ∈
      v.adicCompletionIntegers (I.rec7 l Z).host.F := fun x hx =>
    mat_int F.gl j v hv (F.glevJ.fr j v hv) (F.glevJ.fr_lat j v hv) (F.levJ.Uloc_lev v hx)
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [mat_one]
    exact ChartLevel.redM_one v
  · rw [mat_mul]
    exact ChartLevel.redM_mul v (hint x hx) (hint y hy)

end GlobalTheory.Mem.Col2.TC.LevJRed
end
end
