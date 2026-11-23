module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteSeesawArrowKernelsProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianNegTraceZeroInvHermitianUnimodular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle226
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullOfXiRec
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle092
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle096
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallKernel

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumB skewGram blkU conjU xiV xiV₁ boxB alpha beta)
open GlobalTheory.RouteSeesaw
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem end_finsupp_sum_apply {α β : Type} (A : Module.End ℂ (β → ℂ)) (Θ : α →₀ ℂ) (f : α → β → ℂ) (w : β) :
    A (fun x => Θ.sum fun d c => c * f d x) w = Θ.sum fun d c => c * A (f d) w := by
  have e : (fun x => Θ.sum fun d c => c * f d x) = ∑ d ∈ Θ.support, Θ d • f d := by
    funext x
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]

  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (m + n) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), add_comm, pow_add, mul_assoc, hm, mul_one]

theorem data_theta_small {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') : ∀ d ∈ Θ'.support,
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  have hsupp := Finsupp.support_sum hd
  simp only [Finset.mem_biUnion] at hsupp
  obtain ⟨P, -, hP⟩ := hsupp
  have hsupp2 := Finsupp.support_sum hP
  simp only [Finset.mem_biUnion] at hsupp2
  obtain ⟨d', hd', hd'2⟩ := hsupp2
  have hdd := Finset.mem_singleton.1 (Finsupp.support_single_subset hd'2)
  subst hdd
  obtain ⟨h1, h2⟩ := hloc d' hd'
  have v1 := (ρ.vT_is t (i : ℕ) (j : ℕ) i.2.le j.2).2.theta
  have v2 := (ρ.vX_is (i : ℕ) (j : ℕ) i.2 j.2.le).2.theta
  have t1 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h1.2 v1
  have t2 := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h2.2 v2
  exact ⟨GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _,
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _⟩



theorem seesaw_swapped {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin (spW₁ G i j).rank)
    (e₂ : Fin S'.rank ≃ Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank)
    (hT' : T'.gramᵀ = -((spW₁ G i j).gram.submatrix e₁ e₁))
    (hS' : S'.gram⁻¹ = -((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ.submatrix e₂ e₂))
    (ω : GA D S' × GA D T' →* Module.End ℂ (WO S' T' → ℂ))
    (hω : IsWeilDatumO W.ψ S' T' (alpha G t i j / beta G i j) (alpha G t i j) ω)
    (f₁ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ) (f₂ : WO (G.pS (.chi i j)) (G.pT (.chi i j)) → ℂ)
    (hf₁ : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) f₁)
    (hf₂ : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) f₂)
    (g : GA D (spV G i j)) (u : GA D (spW₁ G i j)) (g₁ : GA D (spV₁ G i j)) (g' : GA D S') (h' : GA D T')
    (hh : Formalism.L2.Theta.mt T' h' = ((Formalism.L2.Theta.mt _ u).map (cA D)).submatrix e₁ e₁)
    (hg : Formalism.L2.Theta.mt S' g' = ((Formalism.L2.Theta.mt _ (GlobalTheory.SquareComm.blk _ _ (g, g₁))⁻¹).submatrix e₂ e₂)ᵀ) :
    W.kerA (.down t i j) f₁ g u * W.kerA (.right i j) f₂ u g₁ =
      xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') (fun x => box2 f₁ (GlobalTheory.SeesawSmall.adjFn (spW₁ G i j) (spV₁ G i j) f₂)
        (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) ((spW₁ G i j).gram.map (incA D)) :
          Matrix (Fin (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank) (Fin (spW₁ G i j).rank) (AE D))) 0 := by
  have r₁ : T'.rank = (spW₁ G i j).rank := by simpa using Fintype.card_congr e₁
  have r₂ : S'.rank = (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).rank := by simpa using Fintype.card_congr e₂
  obtain ⟨ωA, hA⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D W.ψ W.ψ_std (spW₁ G i j)
    (GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)) (alpha G t i j) (alpha G t i j / beta G i j)
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hω.hecT hω.hecS (r₁ ▸ hω.resT) (r₂ ▸ hω.resS)
  obtain ⟨hbox, hker⟩ := GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωA hA f₁ f₂ hf₁ hf₂
  rw [hker g u g₁, GlobalTheory.BigSeesaw.swap_eq _ _ S' T' e₁ e₂ hT' hS' hA hω hbox u _ g' h' hh hg]
  rfl



theorem kerSmall_eq_theta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j))
    (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j)))
    (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁),
    ∀ ΦB, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsDatumB W e Γ Θ' ΦB →
    ∃ ξ : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid (i + 1) j)) → ℂ, (∀ x, ‖ξ x‖ = 1) ∧
      ∀ g u, kerSmall W Θ' g g₁ u =
        ξ (g, g₁) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' ΦB (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU _ (-1) h.JW₁ u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (g, g₁)) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ X om om' h hTr hv Φ hΦ
  refine ⟨fun x => xiV G i j x.1 * xiV₁ G t i j x.2, fun x => ?_, fun g u => ?_⟩
  · simp only [xiV, xiV₁, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.flatDet, norm_mul, Circle.norm_coe, mul_one]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.WeilSchrodingerHerm.main D Bs hTr.base _ Γ.V' _ _ hTr.geo.hV'
  obtain ⟨hJ, LS, hLS, h4, h5, h6⟩ := GlobalTheory.WeilSchrodingerSkew.main D Bs hTr.base _ Γ.W _ _ hTr.geo.hW
  have hξ0 : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have eA : Γ.V'.J = (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]; exact (Matrix.transpose_transpose _).symm
  have e1 : (-D.host.xi0 • Γ.W.J⁻¹)⁻¹ = (-D.host.xi0)⁻¹ • Γ.W.J := Matrix.inv_eq_left_inv (by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_nonsing_inv _ hJ,
      inv_mul_cancel₀ (neg_ne_zero.2 hξ0), one_smul])
  have eB : (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 •
      (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    have e2 : D.host.xi0 • (-D.host.xi0)⁻¹ • Γ.W.J = -Γ.W.J := by
      rw [smul_smul, inv_neg, mul_neg, mul_inv_cancel₀ hξ0, neg_one_smul]
    show (-1 : AF D.host.F ⊗[D.host.F] D.host.E) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (-D.host.xi0 • Γ.W.J⁻¹)⁻¹)
    rw [e1, e2]
    funext a b
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  obtain ⟨ω, hω, -, hth⟩ := GlobalTheory.WeilBridge.exists_theta_eq D Bs hTr.base
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V' Γ.W _ _ _ _
    hTr.geo.hV' hTr.geo.hW eA eB
    Γ.M' hTr.geo.hM' X.α (X.α / X.β) hTr.chars.heckeα (isHecke_div hTr.chars.heckeα hTr.chars.heckeβ) hTr.chars.resα
    (resEtaPow_div hTr.chars.resα hTr.chars.resβ) om' hTr.weil'
  rw [h.ψ, h.α, h.β] at hω
  obtain ⟨g', h', hh', hg'⟩ := GlobalTheory.WeilSchrodinger.match_pair D
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))) Γ.V'.J Γ.W.J (-1) eA eB
    (conjU (spW₁ G i j) (-1) h.JW₁ u) (blkU (spV G i j) (spV₁ G i j) e h.JWW (g, g₁))
  have key := hth _ _ g' h' hh' hg' Φ hΦ.1
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z) key.symm)
  have htr : GlobalTheory.WeilSchrodinger.thetaTr D.host.F Γ.M'.co Bs.ψ Φ =
      fun w => Θ'.sum fun d c => c * boxB e d w := by
    funext w
    show GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho Bs.ψ w Φ) = _
    rw [h.ψ, hΦ.2 w]
    rfl
  refine Eq.trans ?_ (congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * ω (g', h') f 0) htr.symm)
  refine Eq.trans ?_ (congrArg (fun z => xiV G i j g * xiV₁ G t i j g₁ * z)
    (end_finsupp_sum_apply (ω (g', h')) Θ' (boxB e) 0).symm)
  rw [kerSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨t1, t2⟩ := data_theta_small W B ρ t i j hΘ d hd
  let e₂ : Fin ((spW G i j).rank + (spW₁ G i j).rank) ≃ Fin ((spV G i j).rank + (spV₁ G i j).rank) :=
    e.symm.trans finSumFinEquiv
  have hb : ∀ {R : Type} [CommRing R] (A : Matrix (Fin (spV G i j).rank) (Fin (spV G i j).rank) R)
      (B : Matrix (Fin (spV₁ G i j).rank) (Fin (spV₁ G i j).rank) R),
      (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix e₂ e₂ = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := fun A B => by
    ext a b
    simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, e₂]
  have hJ' : Γ.W.J = D.host.xi0 • ((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂ := by
    refine h.JWW.trans (congrArg (D.host.xi0 • ·) ?_)
    rw [GlobalTheory.Doubling.gram_hsum, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← hb]
    rfl
  have hT' : (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0))).gramᵀ =
      -((spW₁ G i j).gram.submatrix (Equiv.refl _) (Equiv.refl _)) := by
    rw [← eA]
    show Γ.V'.J = -(spW₁ G i j).gram
    rw [h.JW₁, neg_one_smul]
  have hS' : (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0))).gram⁻¹ =
      -(((GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)).gramᵀ).submatrix e₂ e₂) := by
    rw [GlobalTheory.WeilSchrodinger.gram_hspOf]
    refine e1.trans ?_
    rw [hJ', smul_smul, inv_neg, neg_mul, inv_mul_cancel₀ hξ0, neg_one_smul]
  have k := seesaw_swapped hL W t i j
    (GlobalTheory.WeilSchrodinger.hspOf D (-D.host.xi0 • Γ.W.J⁻¹) h4 h5 LS hLS h6 (fun _ => (0, 0)))
    (GlobalTheory.WeilSchrodinger.hspOf D Γ.V'.Jᵀ h1 h2 Γ.V'.L hTr.geo.hV'.lat.toIsLattice h3 (fun _ => (0, 0)))
    (Equiv.refl (Fin (spW₁ G i j).rank)) e₂ hT' hS' ω hω d.1.2 d.2 t1 t2 g u g₁
    g' h' hh' (by
      rw [hg', ← map_inv, Prod.inv_mk, GlobalTheory.SquareComm.mt_blk]
      exact congrArg transpose (hb (Formalism.L2.Theta.mt _ g⁻¹) (Formalism.L2.Theta.mt _ g₁⁻¹)).symm)
  refine (congrArg (fun z => Θ' d * z) k).trans ?_
  rw [mul_left_comm]
  refine congrArg (fun f => xiV G i j g * xiV₁ G t i j g₁ * (Θ' d * ω (g', h') f 0)) ?_
  funext x
  exact (GlobalTheory.SeesawSmall.thetaSquareProductRouteB_eq_externalProduct e d x).symm

end GlobalTheory.SmallKernel

end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.RunOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val_eq (D : D7) (y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ((cjFin D y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  have h : D.conjF = D.sp.cm.sig :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin sigR
  rw [h]
  rfl

theorem xi_det_of_isDetRoot {D : D7} {xi de : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ} (h : XiTilde xi de)
    (V : Formalism.BasicNotions.TH.HSp D) (g : Formalism.L2.Theta.GA D V) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.IsDetRoot V g x) :
    xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom V g)) =
      de (Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x) := by
  rw [← GlobalTheory.AntiCycRead.quo_of_isDetRoot D V g x hx, ← h]
  congr 1
  apply GlobalTheory.AntiCycRead.quo_eq_of
  have e : (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) =
      ((Units.map (Formalism.L2.Theta.finPart D).toMonoidHom x : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := rfl
  rw [e, ← cjFin_val_eq, ← Units.val_mul, div_mul_cancel]

theorem exists_run_pins : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), Links2 p → CoreTies L ex.errX p.T (R2 p) → ∀ l : ℕ, (l = D.host.pde ∨ l = D.host.pde') → ∃ r : GlobalTheory.RealIndexBound.RunData p.T, LawsFull r.full ∧ (∀ i : Fin D.R.m, GlobalTheory.FormTies.OneCover r.full.toTop ((i : ℕ) + 1)) ∧ (∀ j n : ℕ, InR D j → (r.full.dδ j n).pd = l) ∧ (∀ i : Fin D.R.m, ∀ γ₀ ∈ Formalism.L2.Theta.GQ (r.full.V ((i : ℕ) + 1) r.full.σ₀), r.full.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (r.full.V ((i : ℕ) + 1) r.full.σ₀) γ₀)) = 1) ∧ ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ i : Fin D.R.m, letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg; RunPin (T := r.full) (R2 p) i (p.κ i).n v (ownAt D v) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ hC l hl

  obtain ⟨δ, hδdef⟩ : ∃ δ : Formalism.L2.Host.HChar D.host.E, δ = if l = D.host.pde then (R2 p).C.del else (R2 p).C.del' :=
    ⟨_, rfl⟩
  have hδ : Formalism.L2.Host.IsDelta (H := D.host) l δ := by
    rcases hl with rfl | rfl
    · rw [hδdef, if_pos rfl]; exact (R2 p).C.isDel
    · rw [hδdef, if_neg D.host.pde_ne.symm]; exact (R2 p).C.isDel'
  have hδv : ∀ x, ((δ.1 x : ℂˣ) : ℂ) ∈ FO D := by
    intro x
    by_cases h : l = D.host.pde
    · rw [hδdef, if_pos h]; exact hC.delVal x
    · rw [hδdef, if_neg h]; exact hC.delVal' x
  obtain ⟨χ, de, hχ, hd, hfin⟩ := GlobalTheory.TameFinitePart.exists_xiRec D l δ hl hδ hδv
  have hF : GlobalTheory.FinalJoin2.FieldOK0 D l := by
    rcases hl with rfl | rfl
    exacts [hC.field₁, hC.field₂]

  obtain ⟨Pk, hPk⟩ := hC.oneHalf
  obtain ⟨P, hP, hPv⟩ : ∃ P : HeightOneSpectrum (𝓞 D.host.K), ((l : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal ∧
      ∀ v ∈ (R2 p).twPl, ownAt D v = l → ∀ PP ∈ placesOver (R2 p) ((R2 p).mu v) (ownAt D v),
        P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
    by_cases hex : ∃ v ∈ (R2 p).twPl, ownAt D v = l
    · obtain ⟨v, hv, hvl⟩ := hex
      refine ⟨Pk l, by rw [← hvl]; exact (hPk v hv).1, fun w hw hwl PP hPP => ?_⟩
      have := (hPk w hw).2 PP hPP
      rwa [hwl] at this
    · have hlp : l.Prime := by
        rcases hl with rfl | rfl
        exacts [D.host.pde_prime, D.host.pde'_prime]
      obtain ⟨P, hP⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hlp
      exact ⟨P, hP, fun w hw hwl => absurd ⟨w, hw, hwl⟩ hex⟩

  have hJ : LawsJ p.T := (fw2 p).laws
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.FinalJoin.exists_top_of_core D p.T.toCore hC.laws hC.rank hF.kpsi
  have hcan : T.Q.Canon := by
    have e : T.toCore.Q = p.T.toCore.Q := congrArg (fun C => C.Q) hTc
    rw [show T.Q = p.T.Q from e]
    exact hC.canon
  obtain ⟨dd, TF, hTF, -, hJ', hxi, hh, hcov⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiRec D p.T T hJ hT hTc hcan l hF P hP de hd
  obtain ⟨r, rfl⟩ : ∃ r : GlobalTheory.RealIndexBound.RunData p.T, r.full = TF := by
    rw [← hJ']
    exact ⟨GlobalTheory.RealIndexBound.RunData.of TF, rfl⟩
  have hInR : ∀ i : Fin D.R.m, InR D ((i : ℕ) + 1) := fun i => ⟨Nat.le_add_left _ _, i.2⟩
  refine ⟨r, hTF, fun i => (hcov _ (hInR i)).1, fun j n hj => (hcov j hj).2 n, ?_, ?_⟩
  · intro i γ₀ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D _).2.2.1 γ₀ hγ
    rw [xi_det_of_isDetRoot hxi _ _ _ hx]
    exact hd.rat _ x rfl
  · intro v hv hvl i
    letI : Algebra r.full.J.Q.c.F D.what₂.LL := p.alg
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [hvl]
      exact (hcov _ (hInR i)).2 _
    · intro PP hPP
      rw [hh]
      exact hPv v hv hvl PP hPP
    · have hδv' : (R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = δ := by
        unfold ownAt at hvl
        unfold Formalism.L2.Host.CharFrame.delAt
        by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
        · rw [if_pos h] at hvl ⊢
          rw [hδdef, ← hvl, if_neg D.host.pde_ne.symm]
        · rw [if_neg h] at hvl ⊢
          rw [hδdef, ← hvl, if_pos rfl]
      refine ⟨χ, hδv' ▸ hχ, fun g x hx => ?_⟩
      rw [xi_det_of_isDetRoot hxi _ _ _ hx]
      exact hfin x _ rfl

end GlobalTheory.RunOnto
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.TowerStep
variable (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B] (e : ℕ)

theorem isGrpPullback_thickMap_factor : IsGrpPullback (thickObj R (maximalIdeal R) e B) (thickObj R (maximalIdeal R) (e + 1) B)
    (spMap (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ maximalIdeal R ^ (e + 1 + 1) →+* R ⧸ maximalIdeal R ^ (e + 1))) (thickMap R (maximalIdeal R) e B) :=
  GlobalTheory.WtTower.isGrpPullback_thickMap (maximalIdeal R) B e

theorem thickMap_fst : thickMap R (maximalIdeal R) e B ≫ pullback.fst B.hom (thick R (maximalIdeal R) (e + 1)) =
    pullback.fst B.hom (thick R (maximalIdeal R) e) :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem isAbelianScheme_thickObj (hB : IsAbelianScheme B) : IsAbelianScheme (thickObj R (maximalIdeal R) (e + 1) B) :=
  GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB (isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1)))

theorem exists_isSquare_thickMap : ∃ i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left,
    IsSquare (thickMap R (maximalIdeal R) e B) i₂ :=
  GlobalTheory.ZM.SiegPull.exists_isSquare (G := thickObj R (maximalIdeal R) (e + 1) B) (G' := thickObj R (maximalIdeal R) e B)
    (f := thickTrans R (maximalIdeal R) e) (pullback.lift_snd _ _ _)

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = 0 := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

theorem isSquare_fst_comp {i₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left}
    {b₂' : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left}
    (si : IsSquare (thickMap R (maximalIdeal R) e B) i₂)
    (sb : IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂') :
    IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) (i₂ ≫ b₂') := by
  have h := GlobalTheory.ZM.SiegPull.isSquare_comp si sb
  rwa [thickMap_fst] at h

end GlobalTheory.TowerStep


open GlobalTheory.TowerStep in
theorem GlobalTheory.TowerStep.step : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (P : LB (G2 B).left), P.IsLB → (∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) → ∀ (e : ℕ) (L : LB (thickObj R (maximalIdeal R) e B).left), L.IsLB → (∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)) → ∃ L' : LB (thickObj R (maximalIdeal R) (e + 1) B).left, L'.IsLB ∧ (∀ b₂ : (G2 (thickObj R (maximalIdeal R) (e + 1) B)).left ⟶ (G2 B).left, IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) (e + 1))) b₂ → LBIso (abelian₂ (thickObj R (maximalIdeal R) (e + 1) B) L') (P.pull b₂)) ∧ LBIso (L'.pull (thickMap R (maximalIdeal R) e B)) L := by
  intro R _ _ B _ _ hB P hP h₁ h₂ e L hL hyp
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R e
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R (e + 1)
  have hπ := Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) :
    maximalIdeal R ^ (e + 1 + 1) ≤ maximalIdeal R ^ (e + 1))
  have gp₁ := isGrpPullback_pullback B (thick R (maximalIdeal R) (e + 1))
  have hab₁ := isAbelianScheme_thickObj R B e hB
  have hgp := isGrpPullback_thickMap_factor R B e
  obtain ⟨b₂', sb⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare gp₁.1.w
  obtain ⟨i₂, si⟩ := exists_isSquare_thickMap R B e
  have s₀ := isSquare_fst_comp R B e si sb
  have hP' : (P.pull b₂').IsLB := pull_isLB hP _
  have hLam : (abelian₂ (thickObj R (maximalIdeal R) e B) L).IsLB := DVR.linComb_isLB _ hL _ _
  have k : LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) ((P.pull b₂').pull i₂) :=
    LBIso.trans hLam (pull_isLB hP _) (pull_isLB hP' _) (hyp _ s₀)
      (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GtBaseChange.lbIso_refl hP') i₂).symm
  obtain ⟨L', hL', hLL⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle _ _ _ hπ (ker_factor_sq (maximalIdeal R) e) (thickObj R (maximalIdeal R) (e + 1) B)
    (thickObj R (maximalIdeal R) e B) (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') L hP' hL k
  obtain ⟨a₁, a₂⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback _ _ B P hP h₁ h₂ (thick R (maximalIdeal R) (e + 1)) (thickObj R (maximalIdeal R) (e + 1) B) _ b₂' gp₁ sb
  have rig := GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient _ _ _ hπ (thickObj R (maximalIdeal R) (e + 1) B) (thickObj R (maximalIdeal R) e B)
    (thickMap R (maximalIdeal R) e B) i₂ hab₁ hgp si (P.pull b₂') hP' a₁ a₂ L' L hL' hL hLL k
  refine ⟨L', hL', fun b₂ hb => ?_, hLL⟩
  rw [GlobalTheory.ZM.SiegPull.isSquare_unique hb sb rfl]
  exact rig
end
