module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle103
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanCosetSumLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle017
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

theorem heckeLin_eq_of_rep {K : Subgroup (GA D V)} {α α' : GA D V} {R R' : Finset (GA D V)}
    (hR : IsCosetRep V (K : Set (GA D V)) α R) (hR' : IsCosetRep V (K : Set (GA D V)) α' R')
    {a b : GA D V} (ha : a ∈ K) (hb : b ∈ K) (hα : α' = a * α * b) {f : GA D V → ℂ}
    (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) : heckeLin V R f = heckeLin V R' f := by
  classical
  have m1 : ∀ γ ∈ R, ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α' * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR.1 γ hγ
    exact ⟨k₁ * a⁻¹, K.mul_mem h₁ (K.inv_mem ha), b⁻¹ * k₂, K.mul_mem (K.inv_mem hb) h₂, by rw [hα]; group⟩
  have m2 : ∀ γ ∈ R', ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR'.1 γ hγ
    exact ⟨k₁ * a, K.mul_mem h₁ ha, b * k₂, K.mul_mem hb h₂, by rw [hα]; group⟩
  have inv : ∀ x y : GA D V, x⁻¹ * y ∈ K → y⁻¹ * x ∈ K := fun x y h => by
    simpa using K.inv_mem h
  funext g
  simp only [heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_bij' (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose)
    (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose_spec.1)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose_spec.1) ?_ ?_ ?_
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have s2 := (hR.2 γ' (m2 γ' s1.1)).exists.choose_spec
    exact (hR.2 γ' (m2 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR.2 γ (m2 γ hγ)).exists.choose_spec
    set γ' := (hR.2 γ (m2 γ hγ)).exists.choose
    have s2 := (hR'.2 γ' (m1 γ' s1.1)).exists.choose_spec
    exact (hR'.2 γ' (m1 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have e : g * γ = g * γ' * (γ'⁻¹ * γ) := by group
    rw [e, hf _ s1.2]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem heckeLin_eq_heckeVec {v : HeightOneSpectrum (𝓞 D.host.F)} {K : Set (GA D V)}
    (hK : ∀ x, x ∈ K ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x)
    (g : GLoc D.sp.cm.sig V.gram v) {R : Finset (GA D V)} (hR : IsCosetRep V K (emb D.sp.cm.sig V.gram v g) R)
    {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) :
    heckeLin V R φ = GlobalTheory.LFun.heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (Formalism.UG.dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  let H : Subgroup (GA D V) := (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v)
  have hKH : K = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  subst hKH
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R₀, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  obtain ⟨s1, s2⟩ := GlobalTheory.LFun.rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  have hR₀ : IsCosetRep V (H : Set (GA D V)) (emb D.sp.cm.sig V.gram v g) (R₀.image (emb D.sp.cm.sig V.gram v)) :=
    ⟨fun γ hγ => ⟨by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y), s1 γ hγ⟩, s2⟩
  have hinv : ∀ k ∈ H, ∀ x, φ (x * k) = φ x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hφ k hk) x
  rw [heckeLin_eq_of_rep hR hR₀ (one_mem H) (one_mem H) (by group) hinv,
    GlobalTheory.LFun.heckeVec_dosetInd hφ (R := R₀) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
  funext x
  rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
  rfl

theorem doubleCoset_of_divAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (hP : IsPrimeIdem P e f)
    {ϖ ϖ' : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal)
    (h2' : ϖ' ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α α' : GA D V}
    (hα : SuppF V f α) (hα' : SuppF V f α') (hD : DivAt V e (ϖ : D.host.E) d α)
    (hD' : DivAt V e (ϖ' : D.host.E) d α') :
    ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V f a ∧ b ∈ KsphC V ∅ ∧ SuppF V f b ∧ α' = a * α * b := by
  rcases id hP with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ :=
      GlobalTheory.SplitLabel.split_label V P e ϖ ϖ' d α α' hi h1 h2 h1' h2' hα hα' hD hD'
    exact ⟨a, b, ha, ha', hb, hb', hab⟩
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).2.2
      ϖ ϖ' d α' h1 h2 h1' h2' hd hα' hD hD'

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem exists_eig {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hJ : SphOff J χ Sb) (B : GlobalTheory.LFun.Fam D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ∃ z : ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ R, Hecke₂ V J χ Sb P d R →
      heckeLin V R f = z • f := by
  classical
  by_cases h : ∃ R, Hecke₂ V J χ Sb P d R
  swap
  · exact ⟨0, fun f _ R hR => absurd ⟨R, hR⟩ h⟩
  obtain ⟨R₀, e₀, f₀, ϖ₀, α₀, hS, hP₀, p1, p2, hd, hJ1, -, hα₀, hD₀, -, hR₀⟩ := h
  have hv : P.under (𝓞 D.host.F) ∉ Sb := GlobalTheory.LFun.offS_iff.1 hS
  have hs := Supp.suppF_iff_of_isPrimeIdem V hP₀ rfl
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f₀ k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F)), emb D.sp.cm.sig V.gram _ k = x :=
    fun x => by
      constructor
      · rintro ⟨m1, m2⟩
        obtain ⟨k, rfl⟩ := (hs x).1 m2
        exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((hJ1 _ m2).1 m1), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have := (hs _).2 ⟨k, rfl⟩
        exact ⟨(hJ1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  let H : Subgroup (GA D V) :=
    (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))).map (emb D.sp.cm.sig V.gram _)
  have hKH : {k | k ∈ J ∧ SuppF V f₀ k} = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  obtain ⟨g₀, rfl⟩ := (hs α₀).1 hα₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.sphericalHeckeOperator_eq_smul_of_localParameter _ _ D.sp.cm.sig V.rank V.gram (frameLat V) _ P rfl (B P) _
    (Formalism.UG.Final.DosetIndMem _ (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))) ℂ g₀)
  refine ⟨z, fun f hf R hR => ?_⟩
  obtain ⟨e, f', ϖ, α, -, hP', q1, q2, -, -, -, hα, hD, -, hRc⟩ := hR
  obtain ⟨rfl, rfl⟩ :=
    ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e₀ f₀ hP₀).2.2.2.1 e f' hP'
  have hpv := hf _ hv P rfl
  have hfix := hpv.mem_fixed
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := doubleCoset_of_divAt hP₀ p1 p2 q1 q2 hd hα₀ hα hD₀ hD
  have hmem : ∀ k, k ∈ KsphC V ∅ → SuppF V f' k → k ∈ H := fun k hk hk' => by
    rw [← SetLike.mem_coe, ← hKH]
    exact ⟨(hJ1 k hk').2 hk, hk'⟩
  have hinv : ∀ k ∈ H, ∀ x, f (x * k) = f x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hfix k hk) x
  rw [hKH] at hRc hR₀
  rw [heckeLin_eq_of_rep hRc hR₀ (H.inv_mem (hmem a ha ha')) (H.inv_mem (hmem b hb hb')) (by rw [hab]; group) hinv,
    heckeLin_eq_heckeVec hK g₀ (hKH ▸ hR₀) hfix, hz _ _ f hpv]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

theorem eig_of_param : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E,
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B →
      ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  intro D V J χ Sb hJ B
  choose a ha using exists_eig (V := V) hJ B
  exact ⟨a, fun f hf P d R hR => ha P d f hf R hR⟩

end GlobalTheory.ParamEigen

end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem standingNumericalData_three_of_dataNW_rankMu : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  intro D hN hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ := hN
  have hW : GlobalTheory.Diag.PG.DuWin D 3 := GlobalTheory.Diag.PG.duWin_three_of_count D fun u => by
    have := hR u
    unfold GlobalTheory.Core.Rk.RankMu at this
    rw [GlobalTheory.Core.Rk.d0_eq] at this
    exact this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hW, h11⟩

end GlobalTheory.Core.Diag
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dataNW_of_standingNumericalData : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  first | exact @GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | exact GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | (intros; apply GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ScalW

theorem znear_term : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  intro D X u
  obtain ⟨c, hc, hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' := X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u with hz'
  have hm' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  refine ⟨c * c, Nat.Coprime.mul_left hc hc, ?_⟩
  intro y hy
  have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' ∈ X.B.I.Lf := by
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (GlobalTheory.St.G.FrameClose.nat_smul_mem c hz0) (GlobalTheory.St.G.FrameClose.mL_le _ hm')
  obtain ⟨t1, ht1, e1⟩ := GlobalTheory.St.G.FrameClose.zmod_of_mL hm' hy
  rw [GlobalTheory.St.G.FrameClose.hA_nat_left, GlobalTheory.St.G.FrameClose.hA_sub_left] at e1
  have hs : hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E := GlobalTheory.St.G.FrameClose.hA_int hz0 hy
  have hs' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E :=
    mul_mem (natCast_mem _ c) hs
  have e : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I z' y • z' - hA X.B.I X.z0 y • X.z0) =
      t1 • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z')) +
      ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0)) := by
    simp only [smul_smul, smul_sub, Nat.cast_mul]
    have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y := by
      linear_combination e1
    have e3 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        t1 * ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) +
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e2
    rw [e3, add_smul, show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) by ring]
    abel
  rw [e]
  refine add_mem ?_ ?_
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, ht1⟩ : IntAf X.B.I.F X.B.I.E) (Submodule.subset_span ⟨_, hcz, rfl⟩)
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, hs'⟩ : IntAf X.B.I.F X.B.I.E) hm'

end GlobalTheory.ScalW
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.EfNear

variable {D : D7} (X : HidaSetting D)

theorem nat_smul_mL (k : ℕ) {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) :
    (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k

theorem dvd_smul_mL {d M : ℕ} (hd : d ∣ M) {x : VA X.B.I}
    (hx : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g) :
    (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x ∈ mL X.B.I X.B.g := by
  obtain ⟨k, rfl⟩ := hd
  rw [Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F), mul_smul]
  exact nat_smul_mL X k hx

theorem term_near {v0 w0 v w y : VA X.B.I} (hw0 : w0 ∈ X.B.I.Lf) (hy : y ∈ X.B.I.Lf) {c1 c2 c3 : ℕ}
    (h1 : (c1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (v0 - v) ∈ mL X.B.I X.B.g)
    (h2 : (c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w) ∈ mL X.B.I X.B.g)
    (h3 : (c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v ∈ X.B.I.Lf) :
    ((c1 * c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I w y • v - hA X.B.I w0 y • v0) ∈
      mL X.B.I X.B.g := by
  have e : hA X.B.I w y • v - hA X.B.I w0 y • v0 =
      -(hA X.B.I w0 y • (v0 - v)) - hA X.B.I (w0 - w) y • v := by
    rw [GlobalTheory.St.G.FrameClose.hA_sub_left, smul_sub, sub_smul]; abel
  rw [e, smul_sub]
  refine sub_mem ?_ ?_
  · refine dvd_smul_mL X (dvd_mul_of_dvd_left (dvd_mul_right c1 c2) c3) ?_
    rw [smul_neg, smul_comm]
    refine neg_mem ?_
    have := (mL X.B.I X.B.g).smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int hw0 hy⟩ : IntAf X.B.I.F X.B.I.E) h1
    rwa [Subring.smul_def] at this
  · refine dvd_smul_mL X (d := c2 * c3) ⟨c1, by ring⟩ ?_
    have e2 : ((c2 * c3 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (w0 - w) y • v) =
        hA X.B.I ((c2 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (w0 - w)) y •
          ((c3 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • v) := by
      rw [GlobalTheory.St.G.FrameClose.hA_nat_left, smul_smul, smul_smul, Nat.cast_mul]
      congr 1; ring
    rw [e2]
    exact Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X (GlobalTheory.St.G.FrameClose.zmod_of_mL h2 hy) h3

end GlobalTheory.ScalW.EfNear

namespace GlobalTheory.ScalW


open GlobalTheory.ScalW.EfNear in
theorem ef_near_ref : ∀ (D : D7) (X : HidaSetting D), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, ∀ a, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a - hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g ∧ (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
  intro D X
  choose c1 hc1 h1 using fun a => (X.basisApprox a).1
  choose c2 hc2 h2 using fun a => (X.basisApprox a).2
  choose c3 hc3 h3 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).1 (X.basisApprox a).1
  choose c4 hc4 h4 using fun a => GlobalTheory.St.G.FrameClose.den_of_inAt (X.vectorsInLattice.1 a).2 (X.basisApprox a).2
  refine ⟨∏ a, c1 a * c2 a * c3 a * c4 a,
    Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (hc1 a) (hc2 a)) (hc3 a)) (hc4 a), ?_⟩
  intro y hy a
  have hdvd : c1 a * c2 a * c3 a * c4 a ∣ ∏ b, c1 b * c2 b * c3 b * c4 b :=
    Finset.dvd_prod_of_mem (fun b => c1 b * c2 b * c3 b * c4 b) (Finset.mem_univ a)
  constructor
  · refine dvd_smul_mL X (d := c1 a * c2 a * c3 a) (dvd_trans ⟨c4 a, rfl⟩ hdvd) ?_
    exact term_near X (v0 := X.e0 a) (w0 := X.f0 a) (v := eV X a) (w := fV X a) (X.vectorsInLattice.1 a).2 hy (h1 a) (h2 a) (h3 a)
  · refine dvd_smul_mL X (d := c2 a * c1 a * c4 a) (dvd_trans ⟨c3 a, by ring⟩ hdvd) ?_
    exact term_near X (v0 := X.f0 a) (w0 := X.e0 a) (v := fV X a) (w := eV X a) (X.vectorsInLattice.1 a).1 hy (h2 a) (h1 a) (h4 a)

end GlobalTheory.ScalW
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.Conj

theorem fixInv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : VA X.B.I)
    (h : X.B.I.fmat (X.xu u) *ᵥ v = v) : X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul X, Matrix.one_mulVec]

theorem prj_conj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  intro D X u y
  have hE : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.eV X a = GlobalTheory.ScalW.eV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).1
  have hF : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.fV X a = GlobalTheory.ScalW.fV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).2
  simp only [GlobalTheory.ScalW.prj, GlobalTheory.St.G.FrameClose.hA_move, hE, hF, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_sum, Matrix.mulVec_smul]

end GlobalTheory.ScalW.Conj
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section
open scoped Classical
open Formalism.MainNotions Formalism.MainNotions.KTwoCosetCount Formalism.MainNotions.MinorIntegralityTorus
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem sum_labels_one_record : ∀ (CH C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), 1 ≤ Cl → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E), (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) → ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b (21 + 4 * |CH|) D.R.m D.R.f ^ ((21 + 4 * |CH|) * (D.R.rS : ℝ)) := by
  intro CH C' Cl Cg cb Cw cT CT C0 D large₂ X Y u hCl1 hH j hj T hTm
  have hfact : ∀ δ ∈ T, (∀ l, IsIntegral ℤ (δ l)) ∧ (∀ l, j < l → δ l = 0) ∧ δ 0 = 1 := by
    intro δ hδ
    obtain ⟨t, -, rfl, rfl⟩ := hTm δ hδ
    exact labFacts_conc t
  have h := kloostermanCosetSum_le Formalism.MainNotions.MinorIntegralityTorus.NormLB_holds Formalism.MainNotions.LatticeSumConvergence.LatSum_holds large₂ hH CH j hj T hfact
  unfold H1C
  refine h.trans ?_
  have hb : 1 ≤ large₂.sc.b := by linarith [KappaEndpoints.two_le_scale_b D large₂]
  have hCl0 : 0 < Cl := by linarith
  have hc0 : 0 ≤ ccOf CH Cl := by unfold ccOf; positivity
  have hcle : ccOf CH Cl ≤ 21 + 4 * |CH| := by
    unfold ccOf
    have : 4 / Cl ≤ 4 := by rw [div_le_iff₀ hCl0]; linarith
    linarith
  unfold Hb
  rw [← Real.rpow_mul (by linarith), ← Real.rpow_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hb
  have hx : 0 ≤ (D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS := by positivity
  have e1 : ccOf CH Cl * (D.R.m : ℝ) ^ 2 * D.R.f * (ccOf CH Cl * D.R.rS) =
      ccOf CH Cl * ccOf CH Cl * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  have e2 : (21 + 4 * |CH|) * (D.R.m : ℝ) ^ 2 * D.R.f * ((21 + 4 * |CH|) * D.R.rS) =
      (21 + 4 * |CH|) * (21 + 4 * |CH|) * ((D.R.m : ℝ) ^ 2 * D.R.f * D.R.rS) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right (mul_le_mul hcle hcle hc0 (by positivity)) hx

end GlobalTheory.Core.Deg
end
end
