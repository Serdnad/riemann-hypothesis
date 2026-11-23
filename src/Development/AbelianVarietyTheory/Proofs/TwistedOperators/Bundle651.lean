module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle650
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle199
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle495
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle215
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle169
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle647
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

theorem _root_.GlobalTheory.T.mem_completedHomLattice_of_mem_latticeHomCoset : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}, IsSelfDualC S ΛS → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → (∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) → ∀ {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {t : WO S T}, t ∈ cosSet e κ → t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | exact GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | (intros; apply GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowChiVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vac_chi_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {i : ℕ}, i + 1 ≤ D.R.m → ∀ (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m)), (∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔ actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) → ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) := by
  intro D T L sc G W U S i hi x y hlat
  have hp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hom := W.om_is (.chi i D.R.m) (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)
  have m1 : (G.toPair (.chi i D.R.m) x y).1 ∈ GfC _ := GlobalTheory.LastRowVac.negGA_mem _ y.2
  have m2 : (G.toPair (.chi i D.R.m) x y).2 ∈ GfC _ := x.2
  have hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      ∃ u₀ ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True),
        u = actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u₀ := by
    intro u
    have e := GlobalTheory.WeilVacMove.actO_inv_actO (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u
    rw [inv_inv, inv_inv] at e
    constructor
    · intro hu
      refine ⟨actO _ _ (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u, (hlat _).2 ?_, e.symm⟩
      rw [e]
      exact hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact (hlat u₀).1 hu₀
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ _ _ _ _ _
    (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m2, Matrix.mul_one, Matrix.one_mul])
    hΛ _ (S.Z.vac_is _ hp)
  obtain ⟨c, -, hc⟩ := GlobalTheory.LastRowVac.eq_smul_vac S hp _ hv'
  exact ⟨c, hc⟩

end GlobalTheory.RowChiVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

section DefOnb

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem gramAt_negSp (V : HSp D) (ρ : D.what₂.Tau) : gramAt D (negSp V) ρ = -gramAt D V ρ := by
  unfold gramAt
  rw [negSp_gram]
  exact Matrix.map_neg _ (map_neg (tauE D ρ)) _

theorem isCartanInv_neg {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : IsCartanInv (-G) (-s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, ?_⟩
  · rw [Matrix.conjTranspose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · rw [neg_mul_neg]; exact h3

theorem defNode_cart_onb {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (X : Node) (hX : DefNode D.R.m X) (ρ : D.what₂.Tau) :
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 := by
  have hC := W.cart_is X hX.inRange ρ
  have hP : (W.onb X ρ)ᴴ * gramAt D (G.V X) ρ * W.onb X ρ = 1 := posOnb_of_defNode W μ0 hL hX ρ
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX.inRange ρ
  have hJ : Formalism.REAL.Jm ε = 1 := h1.symm.trans hP
  rw [hJ, Matrix.mul_one] at h2
  have hn : gramAt D (negSp (G.V X)) ρ = -gramAt D (G.V X) ρ := gramAt_negSp _ _
  refine ⟨hC, ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩, ?_, ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩⟩
  · rw [hP]; simp [Matrix.diagonal_one]
  · rw [h2]; simp [Matrix.diagonal_one]
  · rw [hn]; exact isCartanInv_neg hC
  · rw [hn, Matrix.mul_neg, Matrix.neg_mul, hP]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h]
  · rw [Matrix.neg_mul, h2]
    ext i j
    simp [Matrix.mul_diagonal]

theorem defNode_cart_onb_all : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) (X : Node), DefNode D.R.m X → ∀ ρ,
    IsCartanInv (gramAt D (G.V X) ρ) (W.cart X ρ) ∧ IsONBasis (gramAt D (G.V X) ρ) (W.cart X ρ) (W.onb X ρ) (G.V X).rank ∧
    IsCartanInv (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) ∧
      IsONBasis (gramAt D (negSp (G.V X)) ρ) (-W.cart X ρ) (W.onb X ρ) 0 :=
  fun hL W X hX ρ => defNode_cart_onb hL W X hX ρ

end DefOnb

end GlobalTheory.RowReal
end
end

section

namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

namespace CompanionTheory.Member.ThetaDownProjection

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
open GlobalTheory.ChainEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem thDn_act (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (g : G) (x : (A.fam.R t).S.Forms)
    (v : SmT (R.MY 0)) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) v = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) v) := by
  have hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun t j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hP (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hC.grp.red_R hC.models.jX t g x).elim fun κ hκ => ?_
  have hrel : Rel R t (R.eG g) 0 (thCC t (R.jX t x)) (thCC t (R.jX t ((A.fam.R t).r g x))) :=
    rel_dnFrom hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hS t (R.eG g) (D.R.m - 1)
      (by have := D.R.two_le_m; omega) _ _
      (rel_ioX hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hC.models.νX hC.models.cX hC.models.HX hS t
        (R.eG g) κ hκ.1 _ _ hκ.2)
  exact act_of_rel hC.lev t _ _ _ hrel v

theorem sum_act {K V H M W G : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W] [Fintype G] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (Θ : H →ₗ[ℂ] M →ₗ[ℂ] W) (r : G → Module.End K V) (a : G → W →ₗ[ℂ] W) (c : G → K) (x : V) (v : M)
    (h : ∀ g, Θ (j (r g x)) v = a g (Θ (j x) v)) :
    Θ (j ((∑ g, c g • r g) x)) v = (∑ g, σ (c g) • a g) (Θ (j x) v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, RingHom.id_apply, h]

theorem heckeProjector_fixes_heckeEigenVector (hC : GlobalTheory.Hk3.Core R F) (y : R.HE.H) (f : (R.MY 0).Vec) : R.e0 (R.HE.e y f) = R.HE.e y f := by
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  have h3 := congrArg (fun u : MMap (R.MY 0) => u f) (sub_eq_zero.1 h2)
  exact (postOn_apply _ _ _ _).symm.trans h3

theorem idem_ind {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (h : ∀ f : M.Vec, e (e (u (PiTensorProduct.tprod ℂ f))) = e (u (PiTensorProduct.tprod ℂ f))) (v : SmT M) :
    e (e (u v)) = e (u v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smul, map_smul, map_smul]; exact congrArg (fun z => r • z) (h f)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]


set_option maxHeartbeats 1000000 in
theorem heckeProjector_idempotent_compositeLift (hC : GlobalTheory.Hk3.Core R F) (t : T0) (y : (R.HX t).H) (v : SmT (R.MY 0)) :
    R.e0 (R.e0 (R.thDn t y v)) = R.e0 (R.thDn t y v) := by
  rw [thDn_eq]
  refine idem_ind (R.MY 0) R.e0 _ (fun f => ?_) v
  have h5 := e_Th hC.chain.Th t y f
  exact (congrArg R.e0 h5).symm.trans ((heckeProjector_fixes_heckeEigenVector hC (R.Th t y) f).trans h5)

set_option maxHeartbeats 1000000 in
theorem proj_thDn (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (x : A.fam.amb.FR t)
    (hx : x ∈ (A.fam.R t).goodF A.fam.X) (v : SmT (R.MY 0)) :
    R.e0 (R.thDn t (R.jX t x) v) = R.thDn t (R.jX t x) v := by
  obtain ⟨y, hy⟩ := hx
  rw [goodAt, level_idempotent_bot, mul_one] at hy
  have h : R.thDn t (R.jX t x) v = R.e0 (R.thDn t (R.jX t y) v) := by
    rw [← hy]
    exact sum_act (R.jX t) (R.thDn t) (fun g => (A.fam.R t).r g) _ (fun g => (idemOf A.X).coeff g) y v
      fun g => thDn_act hP hC t g y v
  rw [h]
  exact heckeProjector_idempotent_compositeLift hC t _ v

end CompanionTheory.Member.ThetaDownProjection

end

end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem pX_xLast_castSucc {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k l : Fin σ) :
    (dW.pX ⬝ xLast dW z) k l.castSucc = (1 : Mx D σ σ) k l := by
  rw [← dW.pX_jX]
  simp only [Matrix.mul_apply, SuppShift.xLast_castSucc]

theorem pX_xLast_last {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k : Fin σ) :
    (dW.pX ⬝ xLast dW z) k (Fin.last σ) = 0 := by
  have h : (dW.pX ⬝ xLast dW z) k (Fin.last σ) = ((dW.pX ⬝ dW.j0) *ᵥ ratV z) k := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, SuppShift.xLast_last]
  rw [h, dW.pX_j0, Matrix.zero_mulVec, Pi.zero_apply]

theorem pX_xLast_mul_apply {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    (N : Mx D (σ + 1) (σ + 1)) (k : Fin σ) (j : Fin (σ + 1)) :
    (dW.pX ⬝ (xLast dW z ⬝ N)) k j = N k.castSucc j := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_castSucc, pX_xLast_last, zero_mul, add_zero]
  simp only [pX_xLast_castSucc, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem psiE_idem_entry {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {σ : ℕ}
    (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (LV : Lat V) (LW : Lat W) (LW₀ : Lat W₀)
    {v : Pl D} (hm : MonoAt dW LW LW₀ v) (hp : PrimAt ψ dV LV v) (hc : ColsAt dV (xLast dW z) LV LW v)
    (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ latA W LW (· = v))
    (i j : Fin (σ + 1)) (hij : j.1 = i.1 + 1) : psiE ψ (idem D (· = v) * N i j) = 1 := by
  obtain ⟨-, -, -, -, -, -, f7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hiσ : i.1 < σ := by have := j.2; omega
  set i' : Fin σ := ⟨i.1, hiσ⟩ with hi'
  have hii : i'.castSucc = i := Fin.ext rfl
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : ∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (s * a) ∈ latV V LV (· = v) := by
    intro a ha
    have haA : a ∈ idAt D (· = v) := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul dV ha
    have h1 := hY _ ha
    rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
    have hb : N i j * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ haA
    have h2 : colMul (xLast dW z) i (N i j * a) ∈ latA W LW (· = v) := by
      refine (f7 W LW _).2 ⟨fun k => Ideal.mul_mem_right _ _ hb, fun t ht => ?_⟩
      have h3 := ((f7 W LW _).1 h1).2 t ht
      have h4 := ((hm _).1 h3).1 i'
      have e1 : (dW.pX *ᵥ (t • colMul (xLast dW z ⬝ N) j a)) i' = t * (a * N i j) := by
        rw [Matrix.mulVec_smul, PsiUnit.mulVec_colMul, Pi.smul_apply, smul_eq_mul, colMul,
          pX_xLast_mul_apply dW z N, hii]
      rw [e1] at h4
      convert h4 using 1
      ext k
      simp [colMul, ← hii, SuppShift.xLast_castSucc, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    have h5 := (hc i (N i j * a) hb).2 h2
    have e2 : s * a = N i j * a := by
      rw [hsdef, mul_comm (idem D (· = v)), mul_assoc, (mem_idAt_iff _ a).1 haA]
    rwa [e2]
  have h6 := (hp i j hij s hs).1 key (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_mem_idV_of_lines {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ)
    (z : Fin W₀.rank → D.host.E) (LV : Lat V) (A : AddSubgroup (Fin W.rank → AE D)) (𝔟V 𝔟W : GlobalTheory.SeeSaw.FI D) {v : Pl D}
    (k : Fin σ) (j : Fin (σ + 1)) (hV : ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, colMul dV.jX j a ∈ latV V LV (· = v))
    (hW : ∀ y ∈ A, (dW.pX *ᵥ y) k ∈ GlobalTheory.SeeSaw.idV 𝔟W v) (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ A) :
    ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, N k.castSucc j * a ∈ GlobalTheory.SeeSaw.idV 𝔟W v := by
  intro a ha
  have h1 := hY _ (hV a ha)
  rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
  have h2 := hW _ h1
  rwa [PsiUnit.mulVec_colMul, colMul, pX_xLast_mul_apply dW z N k j, mul_comm] at h2

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem span_neg (x : D.host.E) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-x) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x :=
  (FractionalIdeal.spanSingleton_eq_spanSingleton).2 ⟨-1, by simp⟩

theorem line_ratio (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    I * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) *
      ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1 + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [pow_succ x (k + 1), ← FractionalIdeal.spanSingleton_mul_spanSingleton, pow_succ 𝔞' (k + 1)]
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact pow_ne_zero _ hx
  have h2 : 𝔞' ^ (k + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  have h3 : 𝔞 ^ n ≠ 0 := pow_ne_zero _ h𝔞
  field_simp

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

variable {D : D7}

theorem line_ratio' (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) * I *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1 + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv]
  rw [← line_ratio I 𝔞 𝔞' h𝔞 h𝔞' x hx n k]
  ring

end GlobalTheory.UniStepFB
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → LevelIndexNormC R F := by
  first | exact @GlobalTheory.LevelIndex.levelIndexNormC | exact GlobalTheory.LevelIndex.levelIndexNormC | (intros; apply GlobalTheory.LevelIndex.levelIndexNormC <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem conj_mem_UJ {n : ℕ} (ε : Fin n → Bool) (G fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hJ : frᴴ * Formalism.REAL.Jm ε * fr = G) (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Formalism.REAL.inUJ ε (fr * g * fr⁻¹) := by
  change gᴴ * G * g = G at hg
  unfold Formalism.REAL.inUJ
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (fr * g * fr⁻¹)ᴴ * Formalism.REAL.Jm ε * (fr * g * fr⁻¹)
      = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹ := by rw [hJ, hg]
    _ = ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem cmp_frame_hom : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  intro D θ hθ V S M τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hfi : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  have hif : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have cmul : ∀ g h : GA D V, M.fr τ * cmp θ τ (g * h) * (M.fr τ)⁻¹ =
      (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) * (M.fr τ * cmp θ τ h * (M.fr τ)⁻¹) := by
    intro g h
    have e : cmp θ τ (g * h) = cmp θ τ g * cmp θ τ h := map_mul (GlobalTheory.RowReal.infMatHom V (θ τ)) g h
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), hfi, Matrix.one_mul]
  have cone : M.fr τ * cmp θ τ (1 : GA D V) * (M.fr τ)⁻¹ = 1 := by
    have e : cmp θ τ (1 : GA D V) = 1 := map_one (GlobalTheory.RowReal.infMatHom V (θ τ))
    rw [e, Matrix.mul_one, hif]
  let u : GA D V → (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ := fun g =>
    ⟨M.fr τ * cmp θ τ g * (M.fr τ)⁻¹, M.fr τ * cmp θ τ g⁻¹ * (M.fr τ)⁻¹,
      by rw [← cmul, mul_inv_cancel, cone], by rw [← cmul, inv_mul_cancel, cone]⟩
  have mem : ∀ g, u g ∈ Formalism.REAL.UJ (M.ε τ) := fun g =>
    conj_mem_UJ (M.ε τ) _ _ _ (M.fr_unit τ) (M.fr_gram τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
  refine ⟨{ toFun := fun g => ⟨u g, mem g⟩, map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · apply Subtype.ext; apply Units.ext; exact cone
  · intro g h; apply Subtype.ext; apply Units.ext; exact cmul g h

end GlobalTheory.FibreAtTau
end
