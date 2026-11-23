module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3176
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3180
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074

@[expose] public section

section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (T.R j)), LawsJ T → InR D j → Y.Good e o → Dom a n → S ⊆ (T.cuspA j a n : Set (T.R j)) → GoodW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n) → GoodW Y.U (xiR D) (fun _ => D.sp.W j) Y.dict (wtZ a n) → slope_sq (Y.nrm (wtZ a n)) (Y.latOver (wtZ a n) S) - 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ slope_sq (normW (T.U j) (xiR D) (T.V j) (T.dict j) (wtZ a n)) (latW (T.U j) (wtZ a n) ⊓ ((Submodule.span T.Q.c.F S).comap (cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)).subtype).restrictScalars (𝓞 T.Q.c.F)) := by
  exact @GlobalTheory.CoreRing.slope_sq_latOver_sub_le
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTanShift

theorem spMap_comp_spMap' {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem isLocalRing_sq (K : Type) [Field K] : IsLocalRing (TrivSqZeroExt K (K × K)) :=
  haveI : Nontrivial (TrivSqZeroExt K (K × K)) := TrivSqZeroExt.inl_injective.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_sq (K : Type) [Field K] : IsArtinianRing (TrivSqZeroExt K (K × K)) := by
  haveI : Module.Finite K (TrivSqZeroExt K (K × K)) := inferInstanceAs (Module.Finite K (K × (K × K)))
  exact IsArtinianRing.of_finite K _

theorem pbEq {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h k ζ' s'} {c : SiegPre h k ζ s} {f f' : S' ⟶ S}
    (hc : SiegPB c' c f) (e : f = f') : SiegPB c' c f' := e ▸ hc

theorem shift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  intro g n h3 hodd K _ r β G hG lam κ κ' t c₃ c₁ hκ h₁ h₂ h₃
  subst hκ
  have pull : ∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (s' : S' ⟶ Sp (cycAway n)) (f : S' ⟶ S), f ≫ s = s' →
      ∀ c : SiegPre g n (zetaAway n) s, c.Principal →
        ∃ c' : SiegPre g n (zetaAway n) s', SiegPB c' c f ∧ c'.Principal := by
    intro S S' s s' f hf c hc
    have hf' : f ≫ s = s' ≫ spMap (RingHom.id (cycAway n)) := by rw [spMap_id', Category.comp_id]; exact hf
    have pr := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S S' s s' f rfl hf'
    obtain ⟨c', hcc⟩ := pr.1 c
    exact ⟨c', hcc, pr.2.1 c c' hcc hc⟩
  have base : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] (f : R →ₐ[K] R'),
      spMap f.toRingHom ≫ spMap ((algebraMap K R).comp β) = spMap ((algebraMap K R').comp β) := by
    intro R R' _ _ _ _ f
    rw [spMap_comp_spMap', ← RingHom.comp_assoc]
    congr 2
    ext x
    simp
  let Φ := TrivSqZeroExt.map (LinearMap.prod κ' (t • lam))
  let p₁ := TrivSqZeroExt.map (LinearMap.fst K K K)
  let p₂ := TrivSqZeroExt.map (LinearMap.snd K K K)
  let ι₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let sm := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)
  let mt := TrivSqZeroExt.map (t • LinearMap.id : K →ₗ[K] K)
  let cst : TrivSqZeroExt K (Fin r → K) →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let cD : DualNumber K →+* DualNumber K := (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have e1 : p₁.toRingHom.comp Φ.toRingHom = dirMap κ' := by
    ext x <;> simp [p₁, Φ, dirMap]
  have e2 : p₂.toRingHom.comp Φ.toRingHom = dirMap (t • lam) := by
    ext x <;> simp [p₂, Φ, dirMap]
  have e3 : mt.toRingHom.comp (dirMap lam) = dirMap (t • lam) := by
    ext x <;> simp [mt, dirMap]
  have e4 : mt.toRingHom.comp cst = cst := by
    ext x <;> simp [mt, cst]
  have e6 : p₁.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [p₁, ι₁]
  have e7 : p₂.toRingHom.comp ι₁.toRingHom = cD := by
    ext x <;> simp [p₂, ι₁, cD]
  have e8 : sm.toRingHom.comp Φ.toRingHom = dirMap (κ' + t • lam) := by
    ext x <;> simp [sm, Φ, dirMap]
  have e9 : sm.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [sm, ι₁]
  have e10 : cD.comp (dirMap κ') = cst := by
    ext x <;> simp [cD, cst, dirMap]
  have hconst : constPt (spMap (dirMap lam)) = spMap cst := by
    simp only [constPt, spMap_comp_spMap']
    congr 1
  obtain ⟨c', hc', hc'p⟩ := pull _ _ (spMap (dirMap κ')) (base (TrivSqZeroExt.map κ')) G hG
  obtain ⟨H, hH, hHp⟩ := pull _ _ (spMap Φ.toRingHom) (base Φ) G hG
  obtain ⟨H'', hH'', hH''p⟩ := pull _ _ (spMap ι₁.toRingHom) (base ι₁) c' hc'p
  obtain ⟨C1, hC1, -⟩ := pull _ (spMap p₁.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₁.toRingHom) rfl H hHp
  obtain ⟨C2, hC2, -⟩ := pull _ (spMap p₂.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₂.toRingHom) rfl H hHp
  have hC1G : SiegPB C1 G (spMap (dirMap κ')) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC1) (by rw [spMap_comp_spMap', e1])
  have hC1c' : SiegPB C1 c' (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq hC1G (by rw [Category.id_comp]))
  have hC1H'' : SiegPB C1 H'' (spMap p₁.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC1c' (by rw [spMap_comp_spMap', e6, spMap_id']))
  have hC2G : SiegPB C2 G (spMap (dirMap (t • lam))) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC2) (by rw [spMap_comp_spMap', e2])
  have h₂' : SiegPB c₃ G (spMap cst) := pbEq h₂ hconst
  have hC2m : SiegPB C2 c₃ (spMap mt.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel h₁ (pbEq hC2G (by rw [spMap_comp_spMap', e3]))
  have hC2Gc : SiegPB C2 G (spMap cst) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp h₂' hC2m) (by rw [spMap_comp_spMap', e4])
  have hC2c₃ : SiegPB C2 c₃ (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel h₂' (pbEq hC2Gc (by rw [Category.id_comp]))
  have hc₃c' : SiegPB c₃ c' (spMap cD) :=
    GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq h₂' (by rw [spMap_comp_spMap', e10]))
  have hC2c' : SiegPB C2 c' (spMap cD) := pbEq (GlobalTheory.SiegelPullComp.pb_comp hc₃c' hC2c₃) (by rw [Category.id_comp])
  have hC2H'' : SiegPB C2 H'' (spMap p₂.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC2c' (by rw [spMap_comp_spMap', e7]))
  have hpb := GlobalTheory.T.trivial_square_zero_extension_pullback K (K × K) K K (LinearMap.fst K K K) (LinearMap.snd K K K)
    ⟨fun a b hab => by simpa using hab, fun y => ⟨y, by simp⟩⟩
  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hHH : SiegPB H'' H (𝟙 _) :=
    GlobalTheory.T.principalSiegelObject_determined_over_artinianPinch g n h3 hodd (CommRingCat.of (TrivSqZeroExt K (K × K))) (CommRingCat.of (DualNumber K))
      (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _ hpb (isLocalRing_sq K) (isArtinianRing_sq K)
      hsurj hsurj (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (K × K))).comp β)) H H'' C1 C2 hHp hH''p
      hC1 hC1H'' hC2 hC2H''
  have hc₁H : SiegPB c₁ H (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH (pbEq h₃ (by rw [spMap_comp_spMap', e8]))
  have hc₁H'' : SiegPB c₁ H'' (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hHH (pbEq hc₁H (by rw [Category.comp_id]))
  have hc₁c' : SiegPB c₁ c' (𝟙 _) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH'' hc₁H'') (by rw [spMap_comp_spMap', e9, spMap_id'])
  exact pbEq (GlobalTheory.SiegelPullComp.pb_comp hc' hc₁c') (by rw [Category.id_comp])

end GlobalTheory.SiegTanShift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep

theorem _root_.GlobalTheory.T.conjugateAction_uniformisation_characters : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (a : 𝓞 E), ∃ En : GlobalTheory.UT.EndU P.U.toUnifPre, En.aA = (letI := H.starRing; P.oA.act (H.bar a)) ∧ ∀ x, En.h x = a • x := by
  first | exact @GlobalTheory.USep.conjAct_endU_chars | exact GlobalTheory.USep.conjAct_endU_chars | (intros; apply GlobalTheory.USep.conjAct_endU_chars <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFnSq

theorem c_comp_inv (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c χ).left ≫ (ι[D.P.A]).left = (D.c (-χ)).left := by
  rw [← Over.comp_left]
  congr 1
  have h : D.c χ * D.c (-χ) = 1 := by
    rw [← GlobalTheory.Poinc.ThetaOne.c_zero D, ← add_neg_cancel χ, D.c_add]; rfl
  exact (eq_inv_of_mul_eq_one_right h).symm

theorem c_eq_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (χ : D.X) :
    (D.c (χ + -χ)).left = (η[D.P.A]).left := by
  rw [add_neg_cancel, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]


open GlobalTheory.IntPointFn in
theorem fn_of_theta_sq : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (χ : D.X)
    (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen →
    ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(D.c χ * b).left, (D.c χ).left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    ∀ (τ : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(D.c (χ + -χ)).left, (D.c χ).left, (D.c (-χ)).left, (D.c 0).left]
      ![-1, 1, 1, -1])), τ.IsGen →
    ∃ G : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J →
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom G) =
        sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b * D.c χ).left) z J ^ 2 *
          (val t r z J ^ 2 * val χt r z J ^ 2 * val D.sym (r ≫ (D.c χ).left) z J *
            (val τ r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val := by
  intro V _ _ D θ b χ t ht χt hχt τ hτ
  have hL := D.P.isLB
  have e0 : (D.c 0).left = (η[D.P.A]).left := by rw [GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq]
  have e1 := c_comp_inv V D χ
  have e2 := c_eq_eta V D χ
  have e4 : (b * D.c χ).left = (D.c χ * b).left := by rw [_root_.mul_comm]
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t t) (LB.mulGen D.P.L _ _ _ _ χt χt))
    (LB.pullGen D.P.L _ _ D.sym (D.c χ).left)) (LB.invGen D.P.L _ _ τ))
    (LB.invGen D.P.L _ _ (LB.mulGen D.P.L (Y := Sp V) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig))
  have hu : u.IsGen := by
    refine mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht ht) (mulGen_isGen _ _ _ _ _ _ _ hχt hχt))
      (pullGen_isGen _ _ _ _ D.sym_gen _)) (invGen_isGen _ _ _ _ hτ))
      (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ D.rig_gen D.rig_gen))
  obtain ⟨s', hs'⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_powSec hL (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (b * D.c χ).left 2 u hu (K' := PEmpty) PEmpty.elim PEmpty.elim (fun U _ f => by
      simp only [u, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
        Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, DegPre.gtε,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
        comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec, e0, e1, e2, e4]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      abel)
  obtain ⟨a, ha⟩ := GlobalTheory.Poinc.Sep.ConjPt.exists_fn s'
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a, fun Z r z J hJ => ?_⟩
  have e2' : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom a) = a := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [e2', ← ha, hs' Z r z J hJ]
  congr 1
  simp only [u, val_mul hJ, val_inv, val_pull hJ, rigV]
  simp only [pow_two]

end GlobalTheory.IntPointFnSq
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

open GlobalTheory.Mum.PolTens GlobalTheory.TensBal in
theorem GlobalTheory.Mum.PolTens.tauBal_polTens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w hpr hc hw hpsi
  letI := PowLim.mod xe (symUnitOf W h)
  intro a
  have hA := transpose_mul_eq W h a
  intro u' hu' hn' y y'
  have htr := triv_span xe hpr hc (span_sigP W _ _ hA)
  rw [flat_sigP] at htr
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := htr
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at Q.M.isLB z
  have key := ros_sig hl hpr w hw _ _ u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', tv_sigP Q xe W _ _ (fun y => a • y) (fun y => star a • y) (PowLim.xe_smul xe _ a)
    (PowLim.xe_smul xe _ (star a)) z J y y'] at key
  have prr := prod_ros (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
    (DVR.cP D'.toPre (TK R) y) (DVR.cP D'.toPre (TK R) y') (isoV w z J J')
  have l₁ : DVR.cP D'.toPre (TK R) y ≫ PowLim.act pr hl (TensO.mat _ a) = DVR.cP D'.toPre (TK R) (a • y) := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  have l₂ : DVR.cP D'.toPre (TK R) y' ≫ PowLim.act pr hl (TensO.mat _ (star a)) =
      DVR.cP D'.toPre (TK R) (star a • y') := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  rw [l₁, l₂, ← DVR.cPoint_add, ← DVR.cPoint_add] at prr
  change ∏ k, isoV w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (PowLim.act pr hl (TensO.mat _ a))
    (PowLim.act pr hl (TensO.mat _ (star a))) k) ^ rosatiε k = _ at prr
  rw [prr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_pol xe w hpsi hJ hJ', tau_pol xe w hpsi hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have v0 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 0 = a • y + y' := rfl
  have v1 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 1 = a • y := rfl
  have v2 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 2 = y' := rfl
  have v3 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 3 = y + star a • y' := rfl
  have v4 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 4 = y := rfl
  have v5 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 5 = star a • y' := rfl
  rw [Fin.prod_univ_six] at key
  erw [v0, v1, v2, v3, v4, v5] at key
  simp only [e0, e1, e2, e3, e4, e5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    ∀ i₀ : Fin r,
    letI := PowLim.mod xe (symUnitOf W h)
    ∃ w' : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull
      (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫
        PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left),
      w'.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' =
          lamVal w' (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
            val (D'.toPre.tau (PowLim.xi xe i₀ a) (TensO.binv (symUnitOf W h) • PowLim.xi xe i₀ b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.PolPair.pairing_factor | exact GlobalTheory.Mum.PolPair.pairing_factor | (intros; apply GlobalTheory.Mum.PolPair.pairing_factor <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitExt

theorem exists_fracHom {R R₁ M : Type} [CommRing R] [IsDomain R] [CommRing R₁] [IsDomain R₁] [Field M] [IsAlgClosed M]
    (ρ : R →+* R₁) (hρ : Function.Injective ρ) (hfin : ρ.Finite) (g : R →+* M) (hg : Function.Injective g) :
    ∃ e : FractionRing R₁ →+* M, ∀ r, e (algebraMap R₁ (FractionRing R₁) (ρ r)) = g r := by
  letI : Algebra R R₁ := ρ.toAlgebra
  letI : Algebra R M := g.toAlgebra
  have hinj : Function.Injective (algebraMap R (FractionRing R₁)) := by
    rw [IsScalarTower.algebraMap_eq R R₁ (FractionRing R₁)]
    exact (IsFractionRing.injective R₁ (FractionRing R₁)).comp hρ
  haveI : Module.IsTorsionFree R (FractionRing R₁) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hg
  haveI : Algebra.IsIntegral R R₁ := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : Algebra.IsAlgebraic R R₁ := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R (FractionRing R₁) :=
    (IsFractionRing.isAlgebraic_iff' R R₁ (FractionRing R₁)).1 inferInstance
  refine ⟨(IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).toRingHom, fun r => ?_⟩
  have h := (IsAlgClosed.lift : FractionRing R₁ →ₐ[R] M).commutes r
  rw [IsScalarTower.algebraMap_apply R R₁ (FractionRing R₁)] at h
  exact h

end GlobalTheory.Mum.TraitExt

namespace GlobalTheory.Mum.TraitExt

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem unifTrait_pull : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁]
    (ρ : R →+* R₁), Base R → FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D₁ : DegData R₁ (maximalIdeal R₁)),
    Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₁ : Over (Sp R₁))
    [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G₁ G (spMap ρ) β₁ →
    ∀ L : LB G.left, L.IsLB → UnifTrait D G L → UnifTrait D₁ G₁ (L.pull β₁) := by
  intro R R₁ _ _ _ _ _ _ ρ hR hfin D D₁ hρD G _ _ G₁ _ _ β₁ hG hpb L hL hU
  obtain ⟨hρD⟩ := hρD
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, hφi, hφl, hpb', hLB, ⟨hD⟩⟩ := hU
  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    GlobalTheory.T.exists_finite_complete_trait_extension_of_base R W R₁ hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨eI, heI, -⟩ := grpPullback_iso hpb' (isGrpPullback_pullback G (spMap φ))
    haveI := heI
    exact GlobalTheory.isSemiAbelian_of_grpIso eI (IsSemiAbelian.pullback _ G hG)
  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hP⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hG' U'
  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G' (spMap iw) (pullback.fst G'.hom (specOf iw)) :=
    isGrpPullback_pullback G' (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [spMap_comp, spMap_comp, hcomm]
  have hpb2 := hpb1.comp hpb'
  have hsq : (pullback.fst G'.hom (specOf iw) ≫ β) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hpb'.1.w, ← Category.assoc, pullback.condition]
    rfl
  set β'' : ((Over.pullback (specOf iw)).obj G').left ⟶ G₁.left :=
    hpb.1.lift (pullback.fst G'.hom (specOf iw) ≫ β) (((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁) hsq
    with hβ''
  have hβ1 : β'' ≫ β₁ = pullback.fst G'.hom (specOf iw) ≫ β := hpb.1.lift_fst _ _ _
  have hβ2 : β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj G').hom ≫ spMap φ₁ := hpb.1.lift_snd _ _ _
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj G') G₁ (spMap φ₁) β'' :=
    hpb.cancel (hpb2.congr hsp hβ1.symm) hβ2
  obtain ⟨h, -, -⟩ := GlobalTheory.T.isPullDeg_square_fourth_side R R₁ W W₁ _ _ _ _ hR.1 hfin.1 hAW hAW₁ ρ φ iw φ₁ hcomm hφ₁i hfin.2.1 hφi hiwi
    D D₁ D' D'' hρD hD hD''
  have hw1 : LBIso U''.LG.L
      (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫ pullback.fst G'.hom (specOf iw))) :=
    ⟨hP.lg.choose, hP.lg.choose_spec.1⟩
  have hw2 : LBIso (U'.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj G')).hom.left ≫
      pullback.fst G'.hom (specOf iw))) (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull hLB _ (by simp)
  have hw3 : LBIso (L.pull (pullback.fst G'.hom (specOf iw) ≫ β)) ((L.pull β₁).pull β'') :=
    GlobalTheory.AlgUniq.lbIso_pull_comp hL β₁ β'' _ hβ1
  have hw : LBIso U''.LG.L ((L.pull β₁).pull β'') :=
    LBIso.trans U''.LG.isLB (pull_isLB U'.LG.isLB _) (pull_isLB (pull_isLB hL _) _) hw1
      (LBIso.trans (pull_isLB U'.LG.isLB _) (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) hw2 hw3)
  exact ⟨W₁, inferInstance, inferInstance, inferInstance, φ₁, (Over.pullback (specOf iw)).obj G', inferInstance,
    inferInstance, β'', D'', A'', U'', hW₁, hφ₁i, hφ₁l, hpb3, hw, ⟨h⟩⟩

end GlobalTheory.Mum.TraitExt
end
end
