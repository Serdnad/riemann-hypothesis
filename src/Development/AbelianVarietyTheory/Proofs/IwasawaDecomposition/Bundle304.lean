module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLaws
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle295
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueSubMemInitSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle291
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag.LineOfMap

open GlobalTheory.ProjSpace GlobalTheory.FlagMod

variable {Z : Scheme.{0}} {S : Type} [CommRing S]

theorem resG_refl {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)) : resG X h a = a := by
  show (X.presheaf.map (homOfLE h).op).hom a = a
  rw [show (homOfLE h).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem fnOn_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U)) :
    fnOn ⊤ (ev z U h a) = (z.appLE U ⊤ h).hom a := by
  refine (resG_refl (X := Sp S) le_top _).trans ?_
  exact (Scheme.ΓSpecIso (CommRingCat.of S)).hom_inv_id_apply _

theorem mem_basicOpen_of_isUnit_ev (z : Sp S ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ U) (a : Γ(Z, U))
    (hu : IsUnit (ev z U h a)) (p : Sp S) : z p ∈ Z.basicOpen a := by
  have h1 := Scheme.basicOpen_of_isUnit _ (hu.map (fnOn ⊤))
  rw [fnOn_ev] at h1
  exact (((Scheme.basicOpen_appLE z ⊤ U h a).symm.trans h1).ge (Set.mem_univ p)).2

variable {O : Type} [CommRing O] {N : ℕ}

end GlobalTheory.DRFlag.LineOfMap
end
end

section

noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem signSpace_cut_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N N' p q : ℕ)
    (hN : N = N') (hp : p ≤ N) (hq : N - p = q) :
    signSpace hstar N (cut N p) = stdSpace hstar N' (fun i => decide (p ≤ i.1)) p q := by
  subst hN hq
  rw [signSpace, card_cut_false N p hp, card_cut_true N p hp]
  rfl

theorem signSpace_false_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) :
    signSpace hstar N (fun _ => false) = stdSpace hstar N (fun _ => false) N 0 := by
  simp [signSpace]

def planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (a b : E) (i : Fin h) : Fin N → E :=
  Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + h + i, by omega⟩ : Fin N) b

theorem planeVec_planeVec (N n h p : ℕ) (hN : n + 2 * h ≤ N) (hp : p = n + h) (a b c d : E) (i j : Fin h) :
    diagForm N (cut N p) (planeVec N n h hN a b i) (planeVec N n h hN c d j) =
      if i = j then star a * c - star b * d else 0 := by
  subst hp
  have hi := i.isLt
  have hj := j.isLt
  have c1 : cut N (n + h) ⟨n + i, by omega⟩ = false := by simp [cut]
  have c2 : cut N (n + h) ⟨n + h + i, by omega⟩ = true := by simp [cut]
  simp only [planeVec, map_add (f := _), LinearMap.add_apply, diag_single_single, c1, c2]
  have e1 : ¬ (n + (i : ℕ) = n + h + j) := by omega
  have e2 : ¬ (n + h + (i : ℕ) = n + j) := by omega
  rw [if_neg e1, if_neg e2]
  by_cases hij : i = j
  · subst hij
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have e3 : ¬ (n + (i : ℕ) = n + j) := by omega
    have e4 : ¬ (n + h + (i : ℕ) = n + h + j) := by omega
    rw [if_neg e3, if_neg e4, if_neg hij]
    simp

theorem ext_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (x : Fin n → E) (a b : E)
    (i : Fin h) : diagForm N neg (extTo n N x) (planeVec N n h hN a b i) = 0 := by
  rw [planeVec, map_add (f := _), diag_ext_single, diag_ext_single, add_zero]
  · simp only; omega
  · simp only; omega

theorem single_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (l : Fin N)
    (hl : n + 2 * h ≤ l) (c a b : E) (i : Fin h) :
    diagForm N neg (Pi.single l c) (planeVec N n h hN a b i) = 0 := by
  have hi := i.isLt
  rw [planeVec, map_add (f := _), diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only; omega
  · simp only; omega

end General

section Main

variable (R : Ranks)

theorem rankY_eq_N_add (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem pY_eq_N_add (j : ℕ) (hj : j < R.m) : pY R j = R.N j + (R.m - 1 - j) / 2 := by
  have := rankY_eq_N_add R j hj
  simp only [pY]
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

include hpz in
theorem top_line_norm :
    diagForm (R.N R.m) (fun _ => false)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz) = (T : E) := by
  refine (diag_single_single _ (fun _ => false) _ _ pz pz).trans ?_
  rw [if_pos rfl, ← hpz]
  simp [sgn]

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := ne_of_eq_of_ne (top_line_norm R T pz hpz) (Nat.cast_ne_zero.2 hT.ne_zero)
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_z_norm :
    ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z (spacesNorm R cm T hT pz hpz).z =
      ((spacesNorm R cm T hT pz hpz).T : E) :=
  top_line_norm R T pz hpz

theorem spacesNorm_hasFrame (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  have h1 := rankY_eq_N_add R j hj
  have h2 := pY_eq_N_add R j hj
  have hN : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  refine ⟨planeVec _ _ _ hN (1 : E) 1, planeVec _ _ _ hN (1 / 2 : E) (-(1 / 2)),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans ?_,
    fun i x => ⟨ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i, ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i⟩,
    fun he => ?_⟩
  · split_ifs
    · rw [star_one]; norm_num
    · rfl
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := R.m_even
    have hl : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by omega
    refine ⟨(Pi.single (⟨_, hl⟩ : Fin (R.rankY j)) pz : Fin (R.rankY j) → E), ?_,
      fun x => diag_ext_single _ _ (cut _ (pY R j)) x _ pz (Nat.le_add_right _ _),
      fun i => ⟨single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i,
        single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i⟩⟩
    refine (diag_single_single _ (cut _ (pY R j)) _ _ pz pz).trans ?_
    have c : cut (R.rankY j) (pY R j) ⟨_, hl⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    rw [if_pos rfl, c]
    change _ = -(T : E)
    rw [← hpz]
    simp [sgn]

theorem spacesNorm_coord :
    ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
      (∀ j, (spacesNorm R cm T hT pz hpz).X j = posSpace hstar (R.N j)) ∧
      (spacesNorm R cm T hT pz hpz).X' = posSpace hstar R.rankX' ∧
      (∀ j, (spacesNorm R cm T hT pz hpz).Y j =
        stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
      (∀ j, 1 ≤ j → j ≤ R.m → (spacesNorm R cm T hT pz hpz).W j =
        stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
      ∀ j, (spacesNorm R cm T hT pz hpz).V j =
        stdSpace hstar R.nV (fun _ => (spacesNorm R cm T hT pz hpz).Vneg j)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then 0 else R.nV)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then R.nV else 0) := by
  refine ⟨star_isIntegral, fun _ => rfl, rfl, fun j => ?_, fun j h1 h2 => ?_, fun j => ?_⟩
  · exact signSpace_cut_eq _ _ _ _ _ rfl (Nat.sub_le _ _) (sub_pY R j)
  · have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    refine signSpace_cut_eq _ (R.rankY 0) R.r (R.k + j - 1) (R.m - j) h ?_ ?_ <;> omega
  · exact signSpace_false_eq _ _

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j :=
  spY_sig R j τ

end Main

end GlobalTheory.Mem.DiagSp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩


end GlobalTheory.OneMapRef.ClassScalar
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.Mem.Chr GlobalTheory.Mem.LocTriv GlobalTheory.RayFromArtin
open scoped nonZeroDivisors

namespace GlobalTheory.UnramModulus

theorem inInertia_restrict {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (L : Type) [Field L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K L]
    {v : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (hA : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v) {σ : _root_.Formalism.ConjugateSelfDual.G K Ω}
    (hσ : σ ∈ _root_.ReciprocityTheory.Gal.Ine (F := K) A) : GlobalTheory.NT.InInertia L v (AlgEquiv.restrictNormalHom L σ) := by
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A fun x =>
    (A.valuation_le_one_iff _).1 (valuation_int_le_one A x)
  have hf : ∀ x, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun x =>
    A.valuation_lt_one_iff (f x)
  refine ⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, ⟨?_⟩, fun x => ?_⟩
  · ext x
    rw [Ideal.mem_under, hf, ← hA x, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  · rw [hf]
    have := hσ.2 _ (valuation_int_le_one A x)
    rw [← σ.restrictNormal_commutes L, ← map_sub] at this
    exact this

theorem rayIdl_le {K : Type} [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)) {U : Subgroup (_root_.Neutral.B1.Ideles K)}
    (ho : IsOpen (U : Set (_root_.Neutral.B1.Ideles K))) (hi : infConn K ≤ U)
    (hu : ∀ v x, _root_.Formalism.L2.Host.IsUnitAt v x → _root_.Neutral.B1.localIdele K v x ∈ U) : rayIdl 𝔪 ≤ U := by
  rintro b ⟨hb, -, hb'⟩
  let c : _root_.Neutral.B1.Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) (infPart b)
  have e : b = c * finPartI K b := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
  rw [e]
  refine mul_mem (hi ⟨_, hb', rfl⟩) ?_
  refine (U.isClosed_of_isOpen ho).mem_of_tendsto
    (tendsto_part (a := finPartI K b) hb fun _ => rfl) (Filter.Eventually.of_forall fun S => ?_)
  exact Subgroup.prod_mem _ fun v _ => hu v _ (hb v)

theorem isModulus_top (H : GlobalTheory.Published.GlobalArtinReciprocity) (K M : Type) [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsAbelianGalois K M] (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭)
    (χ : (M ≃ₐ[K] M) →* ℂˣ) : GlobalTheory.NT.IsModulus M χ ⊤ := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := H K Ω
  let j : M →ₐ[K] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra M Ω := j.toRingHom.toAlgebra
  have : IsScalarTower K M Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : CommGroup (M ≃ₐ[K] M) := { (inferInstance : Group (M ≃ₐ[K] M)) with mul_comm := mul_comm' }
  let φ : _root_.Formalism.ConjugateSelfDual.G K Ω →* (M ≃ₐ[K] M) := AlgEquiv.restrictNormalHom M
  have hφ : Continuous φ := by
    refine continuous_of_isOpen_ker' φ ?_
    have : FiniteDimensional K j.fieldRange := j.equivFieldRange.toLinearEquiv.finiteDimensional
    refine Subgroup.isOpen_mono (fun σ hσ => ?_) j.fieldRange.fixingSubgroup_isOpen
    ext x
    apply (algebraMap M Ω).injective
    exact (σ.restrictNormal_commutes M x).trans (hσ ⟨_, x, rfl⟩)
  let θ : _root_.Neutral.B1.Ideles K →* (M ≃ₐ[K] M) := (liftAb φ hφ).comp art
  have hθ : Continuous θ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (θ.ker : Set (_root_.Neutral.B1.Ideles K)) := (isOpen_discrete {1}).preimage hθ
  have hk : (_root_.Neutral.B1.diagUnits K).range ⊔ infConn K ≤ θ.ker := fun x hx => by
    have hk : x ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have hr : rayGrp ⊤ ≤ θ.ker := by
    refine sup_le (le_sup_left.trans hk) (rayIdl_le ⊤ ho (le_sup_right.trans hk) fun v x hx => ?_)
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨τ, hτ, e⟩ := (ha.ine v A hA _).1 ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← e, liftAb_toAb]
    exact hM v _ (inInertia_restrict M hA hτ)
  let ψ : idealsPrimeTo (⊤ : Ideal (𝓞 K)) →* (M ≃ₐ[K] M) := (θ.comp (unifIdl ⊤))⁻¹
  have hψ : ∀ 𝔭 h, GlobalTheory.NT.UnramIn M 𝔭 ∧ GlobalTheory.NT.IsFrob M 𝔭 (ψ (primeElt ⊤ 𝔭 h)) := fun v hv => by
    refine ⟨hM v, ?_⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ, e'⟩ := (ha.frob v A hA _).1 ⟨_, isUnifAt_unif v, rfl⟩
    have : ψ (primeElt ⊤ v hv) = AlgEquiv.restrictNormalHom M σ := by
      rw [MonoidHom.inv_apply, MonoidHom.comp_apply, unifIdl, extend_primeElt, MonoidHom.comp_apply,
        ← e', liftAb_toAb, map_inv, inv_inv]
    rw [this]
    exact isFrob_restrict M hA hσ
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr' => ?_⟩
  · obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob M 𝔭
    rw [GlobalTheory.NT.heckeVal_of_unramIn M χ (hM 𝔭) hσ]
    exact Units.ne_zero _
  · have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr'.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr'.2.1
    obtain ⟨A, hA'⟩ := exists_integral ⊤ _ ha0 hr'.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral ⊤ _ hb0 hr'.2.2.2.1
    rw [heckeIdeal_eq M ⊤ ψ hψ χ _ ha0 A hA', heckeIdeal_eq M ⊤ ψ hψ χ _ hb0 B hB']
    have h1 : B⁻¹ * A ∈ (rayPrincipal ⊤).subgroupOf (idealsPrimeTo (⊤ : Ideal (𝓞 K))) := by
      rw [Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast hr'.1
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hr'.2.1
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr', by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    have h2 : ψ (B⁻¹ * A) = 1 := by
      rw [MonoidHom.inv_apply, inv_eq_one]
      exact hr ((unifIdl_mem_rayGrp_iff top_ne_bot _).2 h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]

theorem isModulus_top_of_isTotallyComplex : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (K M : Type) [Field K]
    [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [Algebra K M] [IsAbelianGalois K M],
    (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn M 𝔭) → ∀ χ : (M ≃ₐ[K] M) →* ℂˣ, GlobalTheory.NT.IsModulus M χ ⊤ :=
  fun H K M _ _ _ _ _ _ _ hM χ => isModulus_top H K M hM χ

end GlobalTheory.UnramModulus

end
end

section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.classLattice_sup_primeDual_localization_eq : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i), loc (A.res v) (Lk A i hi v c) = loc (A.res v) (clsCrd D u i hi c) := by
  first | exact @GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | exact GlobalTheory.LevelHecke.loc_lk_eq_loc_cls | (intros; apply GlobalTheory.LevelHecke.loc_lk_eq_loc_cls <;> assumption)
end
