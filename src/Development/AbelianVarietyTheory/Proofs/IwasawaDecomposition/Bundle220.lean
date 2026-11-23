module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle208
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMinorProductTranslateJointLowestWeight
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.tens_of_forall_isPsEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → IsAmpleLB (tens A N) := by
  intro k _ X f hf A N hA hN hpe
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  have hT : (tens A N).IsLB := isLB_tens hA.isLB hN
  refine isAmpleLB_of_subsingleton_coh_one X (tens A N) hT fun F hF => ?_
  obtain ⟨j₀, hj⟩ := eventually_subsingleton_coh_ample_psEff k X f hf A N hA hN hpe F hF
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have h1 := hj (max j₀ 1) (max j₀ 1) (le_max_left _ _) le_rfl 1 one_pos
  have hpow (L : LB X) (hL : L.IsLB) (n : ℕ) (h : (lbPow L n).IsLB) :
      cls _ h = n • cls L hL := by
    rw [cls_linComb hL, Fintype.sum_unique, pull_id, natCast_zsmul]
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq F
    (isLB_tens (isLB_lbPow hA.isLB (max j₀ 1)) (isLB_lbPow hN (max j₀ 1)))
    (isLB_lbPow hT (max j₀ 1)) (by
      rw [cls_tens (isLB_lbPow hA.isLB _) (isLB_lbPow hN _), hpow A hA.isLB, hpow N hN,
        hpow (tens A N) hT, cls_tens hA.isLB hN, smul_add])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 i).symm.injective.subsingleton

end GlobalTheory
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.InnerLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def InnerSteps : Prop :=
  ∀ t (k : Fin D.R.m), (k : ℕ) + 1 < D.R.m → IsStepWeil k R.ψ (Yc D k) (Yc D (k + 1)) (R.ωY t k) ∧
    IsVacVec R.ψ R.θ (R.MY k) (R.MY (k + 1)) (R.vY t k)

def InnerLaws : Prop :=
  ∀ t k, k + 1 < D.R.m → ∀ κ ∈ levS _ (R.βY k) (R.datYt t k R.triv), κ ∈ GfC (Yc D k) ∧
    R.ωY t k (κ, 1) (R.vY t k) = levChi _ (R.βY k) (R.datYt t k R.triv) κ • R.vY t k

theorem haar_fund (hν : R.models_νY) (hν' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · exact ⟨(hν t j h).1.1, (hν t j h).2⟩
  · have e : j = D.R.m - 1 := by omega
    subst e
    exact ⟨(hν' t).1.1, (hν' t).2⟩

theorem ioYSt_of_inner (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hθ : IsInfFam R.θ) (hS : InnerSteps R)
    (hL : InnerLaws R) (hν : R.models_νY) (hν' : R.models_νY') (hI : R.chain_ItY) : IoYSt R := by
  intro t k hk
  have hk0 : k < D.R.m := by omega
  obtain ⟨hW, hV⟩ := hS t ⟨k, hk0⟩ hk
  exact hP.of_index_eq ⟨k, hk0⟩ (min k D.R.m) (min (k + 1) D.R.m) (min_eq_left hk0.le) (min_eq_left hk.le)
    (Yc D k) (Yc D (k + 1)) (R.MY k) (R.MY (k + 1)) R.θ R.ψ hθ (hC _) (R.ωY t k) (R.vY t k) hW hV
    (R.ItY k) (hI t k hk) _ _ (hL t k hk) _ _ (haar_fund R hν hν' t _ hk).1 (haar_fund R hν hν' t _ hk).2
    _ _ (R.CC t (k + 1)) le_rfl

theorem exists_ioY_of_ioYSt (h : IoYSt R) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY := by
  classical
  have key : ∀ t k, ∃ io : R.CC t (k + 1) →ₗ[ℂ] R.CC t k, k + 1 < D.R.m →
      Lift.IsIo (R.νY t (k + 1)) (R.fdY t (k + 1)) (thetaKO (R.ωY t k)) (R.ptY t k) (R.ItY k)
        (R.CC t (k + 1)) (R.CC t k) io := by
    intro t k
    by_cases hk : k + 1 < D.R.m
    · obtain ⟨io, hio⟩ := h t k hk
      exact ⟨io, fun _ => hio⟩
    · exact ⟨0, fun h' => absurd h' hk⟩
  choose io hio using key
  exact ⟨io, fun t k hk => hio t k (by omega)⟩

theorem exists_ioY_of_pair (hP : IoPair D) (hC : ∀ k, ChainPar D k) (hS : InnerSteps R) (hL : InnerLaws R)
    (hM : R.IsModels) (hI : R.chain_ItY) : ∃ io, ({ R with ioY := io } : RealDat D A Ks).chain_ioY :=
  exists_ioY_of_ioYSt R (ioYSt_of_inner R hP hC hM.inf hS hL hM.νY hM.νY' hI)

end GlobalTheory.Chain.InnerLift

end
end

section

open IsDedekindDomain NumberField

theorem _root_.GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  first | exact @GlobalTheory.LevelChars.LevTriv.levSub_triv | exact GlobalTheory.LevelChars.LevTriv.levSub_triv | (intros; apply GlobalTheory.LevelChars.LevTriv.levSub_triv <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pow_eq_one_of_toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {T : Over S'} (x : T ⟶ G') (N : ℕ)
    (hx : Out.toBase h.1.w x ^ N = 1) : x ^ N = 1 := by
  let β := GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))

theorem pushEx_cubWeil (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ)
    (hk : 0 < k) (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k)) :
    GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b))
      (unitOn ζ) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'

  have tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d => by
    have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z) := fun n z => by
      induction n with
      | zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm
      | succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]
    rw [hpow, Fu.ex_ker i P hP]
    exact ⟨d, by
      ext j
      simp [hk']⟩
  have h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ) :=
    (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2
      (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)
  let f₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let m₀ := Z.m0.toSABMap

  let σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)
  have h₁ := h₀.comp σ
  have e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [σ]
  rw [e₁] at h₁

  let lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
    Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
  have eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z := fun z =>
    Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))
  have tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d =>
    pow_eq_one_of_toBase m₀.cart _ k (by
      rw [eb, ← MonObj.comp_pow, tors, MonObj.comp_one])
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)
  have h₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin
    k _ _ _ ζ' hζ'
  rw [eb, eb] at h₂
  obtain rfl : ζ' = unitOn ζ := h₂.unique h₁
  have h₃ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin
    k _ _ _ _ hζ'

  let τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)
  have h₄ := h₃.comp τ
  have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [τ]
  rw [e₂] at h₄
  have e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z := fun z =>
    Over.OverMorphism.ext (Category.id_comp _)
  rwa [e₃, e₃] at h₄

end GlobalTheory.ShFam.Hor.LogCh
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm


open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes in
theorem weights_of_minors : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  intro D i σ hσ M _
  subst hσ
  have hnr : ∃ s : ℕ, D.R.r + D.R.t = 2 * s := by
    obtain ⟨a, ha⟩ := Formalism.L2.NTheta.odd_r D.R
    obtain ⟨b, hb⟩ := D.R.t_odd
    exact ⟨a + b + 1, by omega⟩
  obtain ⟨s, hs⟩ := hnr
  have hsq : (D.R.r : ℚ) + D.R.t = 2 * s := by exact_mod_cast hs
  choose e he using fun τ : D.what₂.Tau => (D.hc τ).e_int i
  choose d hd using fun τ : D.what₂.Tau => (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).d_int
  refine ⟨fun τ => -e τ + s, fun τ => -e τ - s, fun τ => -d τ, fun τ => ?_⟩
  have A := GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ
  obtain ⟨hpq, hV⟩ := A.rank
  have hVq : ((Vc D i).rank : ℚ) = 2 * s := by rw [hV, hs]; push_cast; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he, hVq]; push_cast; ring
  · rw [he, hVq]; push_cast; ring
  · have := hd τ
    unfold dShift at this
    push_cast
    rw [← this]
    ring
  · have hen := M.enum τ
    rw [GlobalTheory.ThetaFiresProbe.parAt_fixed] at hen
    obtain ⟨hn, hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ hpq) hen
    intro a
    obtain ⟨x, rfl⟩ : ∃ x, a = Fin.cast hn (finSumFinEquiv x) :=
      ⟨finSumFinEquiv.symm (Fin.cast hn.symm a), by simp⟩
    rw [hx x]
    congr 1
    rcases x with c | c
    · have h1 := A.kap_plus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) = (aP D i τ c : ℤ) + (-e τ + s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl c) : ℤ) : ℚ) =
            (((aP D i τ c : ℤ) + (-e τ + s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_pos (by simp)]
      simp
    · have h1 := A.kap_minus c
      rw [hsq, eS, he] at h1
      have h2 : Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
          -(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) := by
        have : ((Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℤ) : ℚ) =
            ((-(aM D i τ (qS D i τ - 1 - c) : ℤ) + (-e τ - s) : ℤ) : ℚ) := by rw [h1]; push_cast; ring
        exact_mod_cast this
      rw [h2]
      unfold wtK
      rw [if_neg (by simp)]
      have h3 : (Wc D i).rank - 1 - ((Fin.cast hn (finSumFinEquiv (Sum.inr c)) : Fin (Wc D i).rank) : ℕ) =
          qS D i τ - 1 - c := by
        simp only [finSumFinEquiv_apply_right, Fin.val_cast, Fin.val_natAdd]
        rw [← hn]
        simp only [qS]
        omega
      rw [h3]
  · intro j
    have h1 := A.coef_eq j
    rw [hd] at h1
    have h2 : (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j = thetaWt D i τ j + d τ := by
      exact_mod_cast h1
    rw [h2]
    have hj := j.2
    unfold wtU thetaWt
    simp only [pS, qS] at hpq ⊢
    by_cases c1 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1
    · have ht := D.R.three_m_lt_t
      rw [if_pos c1, if_pos c1, if_neg (by omega)]
      ring
    · rw [if_neg c1, if_neg c1]
      by_cases c2 : (j : ℕ) < ((Wc D i).sig (tauE D τ)).1 + D.R.t
      · rw [if_pos c2, if_neg (by omega)]
        ring
      · rw [if_neg c2, if_pos (by omega)]
        have h3 : (Vc D i).rank - 1 - (j : ℕ) = ((Wc D i).sig (tauE D τ)).2 - 1 - (j - (((Wc D i).sig (tauE D τ)).1 + D.R.t)) := by
          omega
        rw [h3]
        ring

end GlobalTheory.JointHarm
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.KTypeOp

theorem star_mem_K {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    kᴴ ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have := congrArg Matrix.conjTranspose hk.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ] at this
  exact this.symm

theorem mul_mem_K {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  refine ⟨mul_mem ha.1 hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

theorem exists_op_of_isTau {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w)
    {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P} (hπ : IsHolRep ε B π) :
    ∃ T : W →ₗ[ℂ] Module.End ℂ P, (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧
      ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s, T (τ k s) y = π k (T s y) := by
  obtain ⟨hτ, hbw⟩ := isHolRep_of_isTau h
  obtain ⟨-, ⟨h1, hm⟩, -, ha, hirr, hw, -, -⟩ := h
  have KC := @GlobalTheory.Dec.TauExt.mem_KC n ε
  let Φ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ fun k => τ k.1 w
  let Ψ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] Module.End ℂ P := Finsupp.linearCombination ℂ fun k => π k.1
  have hΦ : ∀ k a, Φ (Finsupp.single k a) = a • τ k.1 w := fun k a => Finsupp.linearCombination_single _ _ _
  have hΨ : ∀ k a, Ψ (Finsupp.single k a) = a • π k.1 := fun k a => Finsupp.linearCombination_single _ _ _
  have hmul : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, τ a (τ b w) = τ (a * b) w := fun a ha' b hb => by
    rw [hm a (KC ha') b (KC hb)]; rfl
  have hw1 : Φ (Finsupp.single ⟨1, GlobalTheory.Dec.TauExt.one_mem_K⟩ 1) = w := by
    rw [hΦ, one_smul, h1]; rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    refine (hirr _ ?_).resolve_left fun h0 => ?_
    · rintro g hg _ ⟨c, rfl⟩
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _)]; exact add_mem ha hb
      | single k a => exact ⟨Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a, by rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]⟩
    · have : w ∈ LinearMap.range Φ := ⟨_, hw1⟩
      rw [h0, Submodule.mem_bot] at this
      simp [this] at hw
  obtain ⟨R, hR⟩ := Φ.exists_rightInverse_of_surjective hsurj
  have hR' : ∀ s, Φ (R s) = s := fun s => LinearMap.congr_fun hR s
  refine ⟨Ψ ∘ₗ R, fun s => ?_, fun y hy => ?_⟩
  · rw [Set.image_eq_range, ← Finsupp.range_linearCombination]
    exact ⟨R s, rfl⟩
  have gram0 : ∀ k k' : Formalism.REAL.Kset ε, B (π k.1 y) (π k'.1 y) = B y y * ⟪τ k.1 w, τ k'.1 w⟫_ℂ := by
    intro k k'
    have hk := star_mem_K k.2
    have e := GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight n ε (-abelian₂) P B π W (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) y y w w hπ hτ hy hy
      hbw hbw _ (mul_mem_K hk k'.2)
    have hww : innerₛₗ ℂ w w = 1 := by
      rw [innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, mul_one] at e
    rw [hπ.2.2.2.1 _ (KC k.2), ha _ (KC k.2), hmul _ hk _ k'.2, ← Module.End.mul_apply,
      ← hπ.2.2.1 _ (KC hk) _ (KC k'.2), e]
    rfl
  have gram : ∀ c c', B (Ψ c y) (Ψ c' y) = B y y * ⟪Φ c, Φ c'⟫_ℂ := by
    intro c c'
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, inner_add_left, mul_add]
    | single k a =>
      induction c' using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb, inner_add_right, mul_add]
      | single k' a' =>
        simp only [hΦ, hΨ, LinearMap.smul_apply, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, inner_smul_right,
          gram0, smul_eq_mul]
        ring
  have key : ∀ c, Ψ (R (Φ c)) y = Ψ c y := by
    intro c
    have := gram (R (Φ c) - c) (R (Φ c) - c)
    rw [map_sub Φ, hR', sub_self, inner_zero_left, mul_zero] at this
    have := hπ.1 _ this
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  refine ⟨?_, fun g hg s => ?_⟩
  · rw [LinearMap.comp_apply, ← hw1, key, hΨ, one_smul, hπ.2.1]; rfl
  · obtain ⟨c, rfl⟩ : s ∈ LinearMap.range Φ := hsurj ▸ Submodule.mem_top
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | single k a =>
      have e : τ g (Φ (Finsupp.single k a)) = Φ (Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a) := by
        rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]
      rw [e, LinearMap.comp_apply, LinearMap.comp_apply, key, key, hΨ, hΨ, hπ.2.2.1 _ (KC hg) _ (KC k.2)]
      simp

theorem exists_op : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ abelian₂ S → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P), IsHolRep ε B π → ∃ (w : S) (T : S →ₗ[ℂ] Module.End ℂ P), w ≠ 0 ∧ (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧ ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' y = π (k.map star) (T s y) := by
  intro n ε abelian₂ H _ _ σ S hσ hS P _ _ B π hπ
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  let w : S := ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, S.smul_mem _ hvS⟩
  have hw : ‖w‖ = 1 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1
    rw [norm_smul]; simp [this]
  have hwt : IsWtOn (Formalism.REAL.Kset ε) σ abelian₂ (w : H) := fun θ hθ => by
    show σ _ (_ • v) = _ • _ • v
    rw [map_smul, hv θ hθ, smul_comm]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε abelian₂ H σ S w hσ hS hw hwt
  obtain ⟨T, hT1, hT2⟩ := exists_op_of_isTau hτ hπ
  refine ⟨w, T, fun h0 => by simp [h0] at hw, hT1, fun y hy => ⟨(hT2 y hy).1, fun k hk s s' hs => ?_⟩⟩
  have hk' := GlobalTheory.Dec.TauExt.conj_mem hk
  rw [← (hT2 y hy).2 _ hk' s]
  congr 2
  apply Subtype.ext
  rw [hτσ _ hk', GlobalTheory.Dec.TauExt.conj_conj, hs]

end GlobalTheory.JointHarm.KTypeOp
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowest_weight_vector_transfer : ∀ (ι : Type) [Fintype ι] (n : ℕ) (ε : ι → Fin n → Bool) (μ : ι → Fin n → ℝ) (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) (P' : Type) [AddCommGroup P'] [Module ℂ P'] (B' : P' →ₗ⋆[ℂ] P' →ₗ[ℂ] ℂ) (ϖ' : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P') (x : P) (x' : P'), IsHolFam ε B ϖ → IsHolFam ε B' ϖ' → IsBotFam ε ϖ μ x → IsBotFam ε ϖ' μ x' → x' ≠ 0 → ∃ ψ : P' →ₗ[ℂ] P, ∀ u : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, u τ ∈ Formalism.REAL.Kset (ε τ)) → ψ (ϖ' u x') = ϖ u x := by
  first | exact @GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | exact GlobalTheory.JointHarm.OrbitMap.exists_orbit_map | (intros; apply GlobalTheory.JointHarm.OrbitMap.exists_orbit_map <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_minorProduct_translate_jointLowestWeight : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  first | exact @GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | exact GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom | (intros; apply GlobalTheory.JointHarm.MinorBottom.exists_joint_bottom <;> assumption)
end
