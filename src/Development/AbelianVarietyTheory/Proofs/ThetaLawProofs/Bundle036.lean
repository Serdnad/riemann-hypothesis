module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle013
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle017
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle040
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.basisBaseChange_relativeBasis_pulledBackSections : ∀ (R R' : Type) [CommRing R] [CommRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (l N : ℕ) (b : Fin N → RR x l) (b' : Fin N → RR x' l), KeyVia x' x f φ w → (∀ k, SecVia x' x φ w (b' k) (b k)) → IsBasis x' b' → GlobalTheory.RelBasis.IndepOn b x'.P.A.hom φ ⊤ ∧ GlobalTheory.RelBasis.SpanOn b x'.P.A.hom φ ⊤ := by
  first | exact @GlobalTheory.RelBasisFibre.main | exact GlobalTheory.RelBasisFibre.main | (intros; apply GlobalTheory.RelBasisFibre.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyPow

theorem exists_isKeyPow : ∀ (R : Type) [CommRing R] (x : KeyIn R) (j : ℕ), 1 ≤ j → ∃ y, GlobalTheory.KeyPow.IsKeyPow y x j := by
  intro R _ x j hj
  have := x.P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R x.P j
  have hr' := hr x.rig x.rig_gen
  have hA : IsAbelianScheme (Out.powObj x.P.A j) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj
    exact AbelianSchemeGerms.isAbelianScheme_powObj x.P.A x.P.isAb n
  let P' : Out.PolAV (Sp R) :=
    { A := Out.powObj x.P.A j
      isAb := hA
      g := j * x.P.g
      smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ j x.P.smoothDim
      L := Out.boxLB x.P.L (Out.powPr x.P.A (n := j))
      isLB := hL
      rigid := ⟨_, hr'⟩
      sym := hS
      ample := relAmple_powObj_boxLB R x.P j
      ktriv := kTriv_boxLB_powObj R x.P j }
  obtain ⟨th, hth, hne⟩ := BoxSection.exists_boxSec _ _ _ j (Out.powIsPowGrp x.P.A j) x.P.L (fun _ => x.th) x.P.isLB
  obtain ⟨v, hv, hvp⟩ := PowLie.isLieBasis_pow R _ _ j x.P.g (Out.powIsPowGrp x.P.A j) x.v x.basis
  refine ⟨⟨P', Nat.mul_pos hj x.g_pos, _, hr', th, fun s => hne s fun _ => x.th_ne s, v, hv⟩,
    ⟨Out.powIsPowGrp x.P.A j, idIso _, idIso_isGen hL⟩, rfl, fun p => hr' p.1 p.2, fun jj b h => ?_, hvp⟩
  refine Eq.trans ?_ (th.compat jj b)
  rw [hth jj fun i => LB.wchart_le x.P.L _ jj i, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (congrArg (fun f => f.hom (x.th.f (jj i))) (Scheme.Hom.appLE_map (Out.powPr x.P.A i).left
    (LB.wchart_le x.P.L (fun i => (Out.powPr x.P.A i).left) jj i) (homOfLE (inf_le_left (b := P'.L.U b))).op)).symm

end GlobalTheory.KeyPow
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyNormalExists

def constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} (a : R) (s : L.Sec) : L.Sec where
  f j := constFn p _ a * s.f j
  compat j k := by
    rw [map_mul, map_mul, ThetaOnto.res_constFn, ThetaOnto.res_constFn, s.compat j k]
    ring

theorem mem_nonzeroLocus_constMul {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X} {a : R}
    (ha : IsUnit a) (s : L.Sec) {z : X} (hz : z ∈ Out.nonzeroLocus s) : z ∈ Out.nonzeroLocus (constMul p a s) := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  have hu : IsUnit (constFn p (L.U i) a) := (ha.map _).map _
  change z ∈ X.basicOpen (constFn p (L.U i) a * s.f i)
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ hu]
  exact ⟨X.basicOpen_le _ hi, hi⟩

theorem isFn_constMul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (a : ℂ) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (h : u.IsFn s θ) : u.IsFn (constMul A.hom a s) (fun z => a * θ z) := by
  intro i z hz
  change valAt' _ _ (constFn A.hom (L.U i) a * s.f i) = _
  rw [valAt'_mul, valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz, h i z hz, _root_.mul_assoc]

theorem exists_normalAt_one (x : KeyIn ℂ) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ} {a b : Fin x.P.g → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hM : M.det ≠ 0) (h : KeyPow.NormalAt x τ M a b c) :
    ∃ th hth v hv, KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (M⁻¹ i)).exists
  refine ⟨constMul x.P.A.hom c⁻¹ x.th, fun s => ?_, v,
    (hb M⁻¹ v x.basis hv).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit), u, h₁, h₂, h₃, h₄, ?_, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, mem_nonzeroLocus_constMul _ (inv_ne_zero hc).isUnit _ hz'⟩
  · have := isFn_constMul u c⁻¹ h₅
    simpa only [inv_mul_cancel_left₀ hc, _root_.one_mul] using this
  · have := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (M⁻¹ i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, M⁻¹ i j • (2 * Real.pi * Complex.I : ℂ)⁻¹ • M j =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) i := by
      rw [← Matrix.nonsing_inv_mul M hM.isUnit]
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at this
    exact this

theorem exists_normalAt :
    ThetaUnifAV → ∀ x : KeyIn ℂ, (∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ GlobalTheory.KeyPow.NormalAt x τ M a b c) ∧ ∃ (th : x.P.L.Sec) (hth : _) (v : _) (hv : _) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), GlobalTheory.KeyPow.charHalf x.P.g a b ∧ GlobalTheory.KeyPow.NormalAt ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, v, hv⟩ τ 1 a b 1 := by
  intro hU x
  obtain ⟨u, Hm, χ, -, hA, hR, hd, -⟩ := hU x.P x.rig x.rig_gen
  choose W hW using fun i => (hd _ (x.basis.1 i)).exists
  obtain ⟨θ, hθ⟩ := KeyPow.exists_isFn x.P.isLB u x.th
  obtain ⟨Fd, hF⟩ := KeyPow.exists_isAddFundamentalDomain u
  obtain ⟨u', τ, M, a, b, c, h₁, h₂, ha, hb, h₃, h₄, hc, h₅, hM, h₆, -⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd _ _ hA hR hθ hW hF rfl rfl
  have hN : KeyPow.NormalAt x τ M a b c := ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩
  obtain ⟨th, hth, v, hv, h⟩ := exists_normalAt_one x hc hM hN
  exact ⟨⟨τ, M, a, b, c, ⟨ha, hb⟩, hc, hM, hN⟩, th, hth, v, hv, τ, a, b, ⟨ha, hb⟩, h⟩

end GlobalTheory.KeyNormalExists
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) : IsLieBasis (fun i : Fin m => v (i.cast e)) := by
  subst e
  exact hv

theorem exists_keyPB_on : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (y : KeyIn R) (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ y.P.A.left) (hg : 1 ≤ P'.g), P'.g = y.P.g → IsGrpPullback P'.A y.P.A (spMap f) φ → LBIso P'.L (y.P.L.pull φ) → ∃ rig hr th hth v hv, KeyPB ⟨P', hg, rig, hr, th, hth, v, hv⟩ y f := by
  intro R R' _ _ f x P' φ hg e h ⟨w, hw₀⟩
  have hL' := P'.isLB
  have hw := (isGen_iff _).1 hw₀
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  have hr₀ : (rigPullOf φ (spMap f) he x.P.L x.rig).IsGen :=
    Out.LBxP.isGen_pullAlong x.P.L φ (spMap f) (fun _ : PUnit => eSec x.P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) x.rig x.rig_gen
  obtain ⟨rig, hr, hm⟩ := Transport.exists_transport (LB.isLB_pull hL' (eSec P'.A))
    (LB.isLB_pull (LB.isLB_pull x.P.isLB φ) (eSec P'.A))
    (LB.linCombIso w (K := PUnit) (fun _ => eSec P'.A) (fun _ => 1)) (DVR.linCombIso_isGen w hw₀ _ _) _ hr₀
  obtain ⟨th', hth'⟩ := sec_pull_down hw x.P.isLB hL' x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  obtain ⟨v', hb', hv'⟩ := exists_isLieBasis_baseChange R R' f x.P.A P'.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  refine ⟨rig, hr, th', fun s => ?_, fun i => v' (i.cast e), isLieBasis_cast e hb',
    φ, he, w, e, Chart.dualMapR f, h, hw₀, hm,
    appLE_eq_of_stalk _ x.th th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨k', hk'⟩ := exists_chart hL' y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨k', hk', ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e' := hth' _ (𝟙 _) y k k' hk hk'
    rw [Category.id_comp] at e'
    exact isUnit_of_mul_isUnit_right (e' ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyTf
end
end
