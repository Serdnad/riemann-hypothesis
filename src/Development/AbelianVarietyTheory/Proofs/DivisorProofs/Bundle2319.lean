module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1026
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Adelic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SectionsFieldChange

open GlobalTheory.AbLaw
open scoped TensorProduct

variable {X Y : Scheme.{0}}

theorem ofSec_secPull {L : LB X} (s : L.Sec) (π : Y ⟶ X) (V : X.Opens) :
    GlobalTheory.LB.ofSec (secPull s π) (π ⁻¹ᵁ V) =
      SecOn.pullLE L π V (π ⁻¹ᵁ V) le_rfl (GlobalTheory.LB.ofSec s V) := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_ofSec, SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  exact GlobalTheory.LB.resG_appLE π _ _ (s.f (j PUnit.unit))

theorem ofSec_smul {L : LB X} (a : Γ(X, ⊤)) (s : L.Sec) (V : X.Opens) :
    GlobalTheory.LB.ofSec (a • s) V = rs X (le_top : V ≤ ⊤) a • GlobalTheory.LB.ofSec s V := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [GlobalTheory.LB.coord_smul, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.smul_f, map_mul, GlobalTheory.resG_resG]
  exact congrArg (· * _) (GlobalTheory.resG_resG _ _ _).symm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev secModule {k : Type} [Field k] (S : LinSys k) : Module k S.L.Sec :=
  Module.compHom _ (algebraMap k Γ(S.Y, ⊤))

attribute [local instance] secModule

theorem secTower {k : Type} [Field k] (S : LinSys k) : IsScalarTower k Γ(S.Y, ⊤) S.L.Sec :=
  ⟨fun a g s => by
    show (algebraMap k Γ(S.Y, ⊤) a * g) • s = algebraMap k Γ(S.Y, ⊤) a • (g • s)
    rw [mul_smul]⟩

attribute [local instance] secTower

theorem isProper_str {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : IsProper S.str := by
  obtain ⟨N, i, hi, e⟩ := hS.proj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str k N
  rw [← e]
  infer_instance

theorem finite_sec {k : Type} [Field k] {S : LinSys k} (hS : S.IsVariety) : Module.Finite k S.L.Sec := by
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) S.L) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj S.isLB
  exact Module.Finite.equiv ((cohZeroTwistEquiv S.L).restrictScalars k)

theorem finrank_baseChange (S : LinSys F) (hS : S.IsVariety) :
    Module.finrank E (S.baseChange E).L.Sec = Module.finrank F S.L.Sec := by
  have := isProper_str hS
  rw [← lineBundleGlobalSectionsDim_eq_finrank, ← lineBundleGlobalSectionsDim_eq_finrank, lineBundleGlobalSectionsDim_def, lineBundleGlobalSectionsDim_def]
  exact FieldChangeInter.hdim_pull (S.isPullback_baseChange E) S.isLB 0

def resTo {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens) :
    L.Sec →+ SecOnR f L V where
  toFun s := SecOnR.of f L V (GlobalTheory.LB.ofSec s V)
  map_zero' := SecOnR.ext fun i => by
    rw [SecOnR.coord_of, GlobalTheory.LB.coord_ofSec, LB.zero_f, map_zero, SecOnR.coord_zero]
  map_add' s t := SecOnR.ext fun i => by
    rw [SecOnR.coord_add, SecOnR.coord_of, SecOnR.coord_of, SecOnR.coord_of, GlobalTheory.LB.coord_ofSec,
      GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, LB.add_f, map_add]

theorem resTo_smul {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (V : X.Opens)
    (a : R) (s : L.Sec) :
    letI := algebraΓOfHom f
    resTo f L V (algebraMap R Γ(X, ⊤) a • s) = a • resTo f L V s :=
  ofSec_smul _ s V

theorem resTo_secPull (S : LinSys F) (E : Type) [Field E] [Algebra F E] (V : S.Y.Opens) (s : S.L.Sec) :
    resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ V) (secPull s (S.bcFst E)) =
      SecOnR.pull S.L (S.isPullback_baseChange E).w V _ le_rfl (resTo S.str S.L V s) :=
  congrArg (SecOnR.of _ _ _) (ofSec_secPull s (S.bcFst E) V)

def pullSecs (S : LinSys F) (E : Type) [Field E] [Algebra F E] {n : ℕ} (b : Fin n → S.L.Sec) :
    Fin n → (S.baseChange E).L.Sec := fun j => secPull (b j) (S.bcFst E)

theorem linearIndependent_secPull (S : LinSys F) (hS : S.IsVariety) {n : ℕ} (b : Fin n → S.L.Sec)
    (hb : LinearIndependent F b) :
    LinearIndependent E (pullSecs S E b) := by
  classical
  have := isProper_str hS
  haveI : CompactSpace S.Y := QuasiCompact.compactSpace_of_compactSpace S.str
  obtain ⟨m, D, hD, hc⟩ := GlobalTheory.exists_fin_affine_cover (X := S.Y) (V := ⊤) isCompact_univ
  have H := S.isPullback_baseChange E
  let R : (Fin n → F) →ₗ[F] (∀ i, SecOnR S.str S.L (D i)) :=
    LinearMap.pi fun i => ∑ j, (LinearMap.proj j).smulRight (resTo S.str S.L (D i) (b j))
  have hRi : ∀ u i, R u i = resTo S.str S.L (D i) (∑ j, u j • b j) := fun u i => by

    rw [map_sum]
    simp only [R, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    exact Finset.sum_congr rfl fun j _ => (resTo_smul S.str S.L (D i) (u j) (b j)).symm
  have hR : Function.Injective R := by
    refine (injective_iff_map_eq_zero R).2 fun u hu => ?_
    have h2 : ∑ j, u j • b j = 0 := by
      refine (SecOn.ofSec_bijective (M := S.L) (V := ⊤) rfl).injective ?_
      refine SecOn.ext_of_cover D (fun _ => le_top) hc.ge fun a => ?_
      rw [SecOn.restrict_ofSec, SecOn.restrict_ofSec]
      have := (hRi u a).symm.trans (congrFun hu a)
      exact this.trans (map_zero (resTo S.str S.L (D a))).symm
    funext j
    exact Fintype.linearIndependent_iff.1 hb u h2 j
  let Bc : ∀ i, E ⊗[F] SecOnR S.str S.L (D i) →ₗ[E]
      SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) := fun i =>
    SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
  have hBc : ∀ i, Function.Bijective (Bc i) := fun i =>
    SecOnR.baseChangeHom_bijective S.isLB H (hD i) rfl
  let Φ : (Fin n → E) →ₗ[E] ∀ i, SecOnR (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) :=
    LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) ∘ₗ
      (TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).toLinearMap ∘ₗ
      R.baseChange E ∘ₗ (TensorProduct.piScalarRight F E E (Fin n)).symm.toLinearMap
  have hΦ : Function.Injective Φ := by
    have h1 : Function.Injective (R.baseChange E) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap R hR
    have h2 : Function.Injective (LinearMap.pi (fun i => Bc i ∘ₗ LinearMap.proj i) :
        (∀ i, E ⊗[F] SecOnR S.str S.L (D i)) →ₗ[E] _) :=
      fun x y h => funext fun i => (hBc i).1 (congrFun h i)
    exact h2.comp ((TensorProduct.piRight F E E fun i => SecOnR S.str S.L (D i)).injective.comp
      (h1.comp (TensorProduct.piScalarRight F E E (Fin n)).symm.injective))
  have hΦc : ∀ c : Fin n → E, Φ c = fun i =>
      resTo (S.baseChange E).str (S.baseChange E).L (S.bcFst E ⁻¹ᵁ D i) (∑ j, c j • pullSecs S E b j) := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]

    rw [map_sum]
    funext i

    rw [Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Φ, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piScalarRight_symm_single,
      LinearMap.baseChange_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
      LinearMap.pi_apply, LinearMap.proj_apply, Bc, SecOnR.baseChangeHom_tmul]
    change SecOnR.baseChangeHom S.L H.w (D i) (S.bcFst E ⁻¹ᵁ D i) le_rfl
      (c j ⊗ₜ[F] R (Pi.single j 1) i) = _
    rw [SecOnR.baseChangeHom_tmul, hRi]
    have hs : ∑ k, (Pi.single j (1 : F) : Fin n → F) k • b k = b j := by
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]
    rw [hs, ← resTo_secPull]
    exact (resTo_smul _ _ _ (c j) _).symm
  refine Fintype.linearIndependent_iff.2 fun c hc => ?_
  have h0 : Φ c = Φ 0 := by
    rw [hΦc, hc, map_zero]
    funext i
    exact map_zero _
  exact congrFun (hΦ h0)

theorem exists_pullSecs_spanning : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (S : LinSys F),
    S.IsVariety → ∃ (n : ℕ) (b : Fin n → S.L.Sec), ∀ t : (S.baseChange E).L.Sec, ∃ u : Fin n → E,
      (({ S with N := n, b := b } : LinSys F).baseChange E).comb u = t := by
  intro F E _ _ _ S hS
  haveI := finite_sec hS
  haveI : Module.Finite E (S.baseChange E).L.Sec := finite_sec (hS.baseChange E)
  let B := Module.finBasis F S.L.Sec
  refine ⟨_, B, fun t => ?_⟩
  have hli := linearIndependent_secPull (E := E) S hS B B.linearIndependent
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, finrank_baseChange S hS])
  have ht : t ∈ Submodule.span E (Set.range (pullSecs S E B)) := hsp ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ht
  exact ⟨u, hu⟩

end GlobalTheory.SectionsFieldChange
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ManyTorsionProper

theorem isProper_of_many_torsion_charZero : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ _ G _ hG g hg m s hs hcard
  by_contra hnp
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hcard
    · exact h
  obtain ⟨P, hP, u, a, b, hu, hab⟩ := GlobalTheory.T.exists_nonconstant_rational_curve_nonproper_group k G hG hnp
  obtain ⟨k', _, _, p, _, _, G', _, hG', hg', hm', ⟨s', hs', hc'⟩, P', hP', u', a', b', hu', hab'⟩ :=
    GlobalTheory.T.exists_charP_specialization_smooth_commGroup_curve k G hG g hg m hm s hs P hP u a b hu hab
  have hpr : IsProper G'.hom :=
    GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP k' p G' hG' g hg' m hm' s' hs' (by rw [hc']; exact hcard)
  exact hab' (GlobalTheory.T.morphism_open_affine_line_abelianScheme_const k' G' (GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G' hG' hpr) P' hP' u' a' b' hu')

end GlobalTheory.ManyTorsionProper
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem exists_j_of_mem_flagOpen (X : FlagCover Y) {y : X.YY} (hy : y ∈ flagOpen X) :
    ∃ x : Xo.XF c, X.π y = Y.j x := by
  obtain ⟨w, rfl⟩ := (opensRange_inc X).ge hy
  refine ⟨(pullback.snd X.π Y.j) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

theorem j_mem_closure_iff {s : Set (Xo.XF c)} (hs : IsClosed s) (x : Xo.XF c) :
    Y.j x ∈ closure (Y.j '' s) ↔ x ∈ s :=
  Set.ext_iff.1 (Y.j.isOpenEmbedding.isOpenMap.preimage_closure_image Y.j.isOpenEmbedding.injective Y.j.continuous _ hs) x

section Ext

variable (X : FlagCover Y) (Z : Comp Xo c)

def openOn : X.YY.Opens := flagOpen X ⊓ X.π ⁻¹ᵁ barComp Y Z

def openOff : X.YY.Opens :=
  flagOpen X ⊓ X.π ⁻¹ᵁ ⟨(closure (Y.j '' (Z : Set (Xo.XF c))))ᶜ, isClosed_closure.isOpen_compl⟩

theorem flagOpen_le_sup : flagOpen X ≤ openOn X Z ⊔ openOff X Z := fun y hy => by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X hy
  by_cases hZ : x ∈ (Z : Set (Xo.XF c))
  · refine Or.inl ⟨hy, ?_⟩
    show X.π y ∈ barComp Y Z
    rw [hx]; exact (j_mem_barComp Z x).2 hZ
  · refine Or.inr ⟨hy, ?_⟩
    show X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
    rw [hx, j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2)]
    exact hZ

theorem not_mem_openOn_openOff {y : X.YY} (h₁ : y ∈ openOn X Z) (h₂ : y ∈ openOff X Z) : False := by
  obtain ⟨x, hx⟩ := exists_j_of_mem_flagOpen X h₁.1
  have a : X.π y ∈ barComp Y Z := h₁.2
  have b : X.π y ∉ closure (Y.j '' (Z : Set (Xo.XF c))) := h₂.2
  rw [hx] at a b
  exact b (subset_closure ⟨x, (j_mem_barComp Z x).1 a, rfl⟩)

end Ext

section Glue

variable {X : FlagCover Y} {Z : Comp Xo c} {e : Ix Dw → ℤ}

theorem exists_extZero (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)) :
    ∃ m' : H0 (flagStr X) (X.LL e) (flagOpen X),
      H0.pull (inc₀ X Z) le_rfl m' = m ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X.YY) (k : X.F.J)
        (hO : ⊤ ≤ x ⁻¹ᵁ flagOpen X) (hk : ⊤ ≤ x ⁻¹ᵁ X.F.U k), ⊤ ≤ x ⁻¹ᵁ openOff X Z →
        H0.val (B := X.LL e) x k hO hk m' = 0 := by
  have hiso : IsoOver (inc₀ X Z) (openOn X Z) := isoOver_of_isOpenImmersion _ (by
    rw [Scheme.Opens.opensRange_ι]; exact inf_le_right)
  have e₁ : U₀ X Z ≤ inc₀ X Z ⁻¹ᵁ openOn X Z := fun z hz => ⟨hz, z.2⟩
  have e₂ : inc₀ X Z ⁻¹ᵁ openOn X Z ≤ U₀ X Z := fun z hz => hz.1
  obtain ⟨m₁, hm₁⟩ := (hiso.bijective_pull (p := flagStr X) (X.F.isLB_LL e) e₁ e₂).2 m
  let W : Bool → X.YY.Opens := fun b => Bool.rec (openOff X Z) (openOn X Z) b
  have hW : ∀ b, W b ≤ flagOpen X := fun b => by cases b <;> exact inf_le_left
  have hc : flagOpen X ≤ iSup W := fun y hy => by
    rcases flagOpen_le_sup X Z hy with h | h
    · exact Opens.mem_iSup.2 ⟨true, h⟩
    · exact Opens.mem_iSup.2 ⟨false, h⟩
  let s : ∀ b, H0 (flagStr X) (X.LL e) (W b) := fun b => Bool.rec (motive := fun b => H0 (flagStr X) (X.LL e) (W b)) 0 m₁ b
  obtain ⟨m', hm'⟩ := GlobalTheory.LB.exists_mod_of_cover (F := GlobalTheory.LB.toMod (X.LL e)) W hW hc s (by
    rintro (_ | _) (_ | _)
    · rfl
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.2 hy.1).elim
    · exact H0.ext_germ (p := flagStr X) fun y hy => (not_mem_openOn_openOff X Z hy.1 hy.2).elim
    · rfl)
  have r₁ : H0.restr (p := flagStr X) (hW true) m' = m₁ := hm' true
  have r₂ : H0.restr (p := flagStr X) (hW false) m' = 0 := hm' false
  refine ⟨m', ?_, fun S _ x k hO hk hx => ?_⟩
  · have h₃ : H0.pull (p := flagStr X) (inc₀ X Z) e₁ (H0.restr (p := flagStr X) (hW true) m') =
        H0.pull (p := flagStr X) (inc₀ X Z) le_rfl m' := H0.pull_restr _ _ _ _
    rw [r₁] at h₃
    exact h₃.symm.trans hm₁
  · have a := GlobalTheory.TangentOrigin.evalPt_res x (inf_le_inf_right _ (hW false)) (GlobalTheory.FlagMod.le_preimage_inf hO hk)
      (GlobalTheory.FlagMod.le_preimage_inf hx hk) (H0.loc (p := flagStr X) m' k)
    refine a.symm.trans ?_
    change H0.val (B := X.LL e) x k hx hk (H0.restr (p := flagStr X) (hW false) m') = 0
    rw [r₂, map_zero]

end Glue

theorem exists_suppOn_sec₀_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (e : Ix Dw → ℤ) (m : H0 (str₀ X Z) (LL₀ X Z e) (U₀ X Z)), ∃ f : GlobalTheory.AllWt.secZ Xo c e, (f : Rul Xo c) ∈ GlobalTheory.AllWt.suppOn Z ∧ sec₀ X Z e f = m := by
  intro E _ _ _ H Dw l Xo c Y X Z e m
  obtain ⟨m', h₁, h₂⟩ := exists_extZero m
  refine ⟨(secOf X e).symm m', ?_, ?_⟩
  · intro S _ _ y hy
    have hv : FlagCover.val (toSecO m') y = 0 := by
      refine (FlagCover.IsVal.eq_val fun S' _ _ ψ P' hP k hz Q t hQ ht => ?_).symm
      have hO := FlagMod.le_preimage_map (z := X.pt P') X.inc (top_le_inc X) le_top
      rw [map_zero, coef_toSecO _ _ _ _ hO, h₂ _ _ _ _ _ ?_, mul_zero]
      intro s _
      refine ⟨hO (Set.mem_univ s), ?_⟩
      show X.π ((X.pt P' ≫ X.inc) s) ∉ closure (Y.j '' (Z : Set (Xo.XF c)))
      rw [FlagCover.pt_inc, ← Scheme.Hom.comp_apply, (X.lies_ptY P').1, Scheme.Hom.comp_apply,
        j_mem_closure_iff (isClosed_of_mem_irreducibleComponents _ Z.2), ← FlagMod.frX_frMap hP,
        Scheme.Hom.comp_apply]
      exact hy _
    change evR Xo c (FlagCover.toRule (toSecO m')) y = 0
    by_cases hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    · rw [FlagCover.evR_toRule _ y hT, hv]
    · unfold evR evalAt
      rw [dite_eq_right hT]
  · show H0.pull (inc₀ X Z) le_rfl ((secOf X e) ((secOf X e).symm m')) = m
    rw [LinearEquiv.apply_symm_apply]
    exact h₁

end GlobalTheory.CompHS
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

set_option autoImplicit false

namespace GlobalTheory.CompHS

theorem exists_generisation_of_mem_closure {T : Type} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T]
    {U : Set T} (hU : IsOpen U) {y : T} (hy : y ∈ closure U) : ∃ g ∈ U, g ⤳ y := by
  haveI : NoetherianSpace (closure U) := NoetherianSpace.set _
  haveI : QuasiSober (closure U) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  have hd : Dense (Subtype.val ⁻¹' U : Set (closure U)) := fun z => by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right subset_closure]
    exact z.2
  have hC := irreducibleComponent_mem_irreducibleComponents (⟨y, hy⟩ : closure U)
  have hg := (isIrreducible_irreducibleComponent (x := (⟨y, hy⟩ : closure U))).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  obtain ⟨o, ho, hne, hle⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨p, hp, hpU⟩ := hd.inter_open_nonempty o ho hne
  have hU' : IsOpen (Subtype.val ⁻¹' U : Set (closure U)) := hU.preimage continuous_subtype_val
  exact ⟨_, (hg.mem_open_set_iff hU').2 ⟨p, hle hp, hpU⟩,
    (hg.specializes mem_irreducibleComponent).map continuous_subtype_val⟩

theorem exists_generic_generisation (X : Scheme.{0}) (x : X) (hd : IsDomain (X.presheaf.stalk x)) :
    ∃ ξ : X, ∀ y, y ⤳ x → ξ ⤳ y := by
  let η : PrimeSpectrum (X.presheaf.stalk x) := ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨X.fromSpecStalk x η, fun y hy => ?_⟩
  have : y ∈ Set.range (X.fromSpecStalk x) := by rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨q, rfl⟩ := this
  exact ((PrimeSpectrum.le_iff_specializes η q).1 (show (⊥ : Ideal _) ≤ _ from bot_le)).map
    (X.fromSpecStalk x).continuous

theorem mem_barComp_of_specializes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (x : Xo.XF c), x ∈ (Z : Set (Xo.XF c)) → ∀ b : Y.X, Y.j x ⤳ b → b ∈ barComp Y Z := by
  intro E _ _ _ H Dw l Xo c Y Z x hx b hb
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str c.F N
    rw [← e]
    infer_instance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := {}
  intro hcl
  have hopen := Y.j.isOpenEmbedding.isOpenMap
  have hc := (TrivOrderTieCompare.isClopen_comp Z)
  obtain ⟨w, hw, hwb⟩ := exists_generisation_of_mem_closure (hopen _ hc.compl.isOpen) hcl
  obtain ⟨ξ, hξ⟩ := exists_generic_generisation Y.X b (Y.normal b).1
  obtain ⟨u, hu, rfl⟩ := (hξ w hwb).mem_open (hopen _ hc.compl.isOpen) hw
  obtain ⟨v, hv, hv'⟩ := (hξ _ hb).mem_open (hopen _ hc.isOpen) ⟨x, hx, rfl⟩
  exact hu (Y.j.isOpenEmbedding.injective hv' ▸ hv)

end GlobalTheory.CompHS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.nonempty_moduliMap_of_marked_period_isometry : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  first | exact @GlobalTheory.HTIso.nonempty_objMap_of_markedIsom | exact GlobalTheory.HTIso.nonempty_objMap_of_markedIsom | (intros; apply GlobalTheory.HTIso.nonempty_objMap_of_markedIsom <;> assumption)
end
