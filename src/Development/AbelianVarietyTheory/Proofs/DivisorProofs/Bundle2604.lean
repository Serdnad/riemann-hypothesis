module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle017
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle635
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle027
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle023
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle039
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels Formalism.L2.Pj
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)

namespace GlobalTheory.KeyFramePoint


open scoped CategoryTheory.MonObj in
theorem card_eq_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] [Nontrivial R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n n' : ℕ} {v : Fin n → (epsR R ⟶ G')} {v' : Fin n' → (epsR R ⟶ G')}
    (hb : IsLieBasis v) (hb' : IsLieBasis v') : n = n' := by
  obtain ⟨b₁⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb
  obtain ⟨b₂⟩ := GlobalTheory.KeyAtEx.nonempty_basis_of_isLieBasis h hb'
  simpa using Fintype.card_congr (b₁.indexEquiv b₂)

theorem exists_keyAt_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : GChart Y) (V K : Type) [CommRing V] [IsLocalRing V] [Field K] [CharZero K] [Algebra V K] (yt : Sp V ⟶ Y.X) (hz : ⊤ ≤ yt ⁻¹ᵁ M.U) (t : SAB H (Sp V)) (_ : SABMap t Y.t yt) (n : ℕ) (w : Fin n → (epsR V ⟶ t.G)), IsLieBasis w → ∀ (θ : t.PP.L.Sec) (x : KeyIn K), IsFibreOf x t.G t.PP.L t.PP.rig θ w (algebraMap V K) → Generates (X := t.G) θ → ∃ (x' : KeyIn K) (a d : Vˣ), KeyAt M (spMap (algebraMap V K) ≫ yt) (le_preimage_comp _ hz) x' ∧ ∀ κ : KeyRule, IsKeyRule κ → algebraMap V K a ^ 8 * (κ K x' : K) = algebraMap V K d ^ 4 * (κ K x : K) := by
  intro E _ _ _ H D l Xo c O _ β Y M V K _ _ _ _ _ yt hz t m n w hw θ x hx hgen
  obtain ⟨w₁, θM, ⟨hw₁, hr₁⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t yt m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev yt M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev yt M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨vM, hvM, hbM, -⟩ := M.lie V (ev yt M.U hz) t m'
  rw [hm'] at hvM
  have he : eSec t.G ≫ m.φ = yt ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ yt he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp V ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr₁

  obtain ⟨a, ha, -⟩ := hgen θM
  have hau : IsUnit a := by
    obtain ⟨g, i, h₁, h₂⟩ := hne (IsLocalRing.closedPoint V)
    exact (NonzeroClosed.of_isMul ha ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩).1
  obtain ⟨a, rfl⟩ := hau

  obtain ⟨P, hP, rig, hrig', th, hthne, v, hv⟩ := x
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := hx
  dsimp only at φ' he' w' hg' hp' hw' hr' hs' hv'
  subst hg'
  have hn : P.g = M.n := card_eq_of_isLieBasis m.cart hw hbM
  have hbM' : IsLieBasis (fun i : Fin P.g => vM (i.cast hn)) := by
    have key : ∀ (k : ℕ) (h : k = M.n), IsLieBasis (fun i : Fin k => vM (i.cast h)) := by
      rintro k rfl
      exact hbM
    exact key _ hn
  choose Mat hMat using fun i : Fin P.g => (hw.2 _ (hbM'.1 i)).exists
  obtain ⟨d, hd⟩ : IsUnit (Matrix.det (Matrix.of Mat)) :=
    ((GlobalTheory.LieComb.lieComb_algebra V t.G P.g w hw.1).2.2.2.2 (Matrix.of Mat) _ hw hMat).1 hbM'
  haveI := P.isAb.comm
  obtain ⟨ex, -, -, -, bas⟩ := GlobalTheory.LieComb.lieComb_algebra K P.A P.g v hv.1
  choose v' hvv' using fun i => (ex (((Matrix.of Mat).map (algebraMap V K)) i)).exists
  have hdet : ((Matrix.of Mat).map (algebraMap V K)).det = algebraMap V K d := by
    rw [hd, RingHom.map_det]; rfl
  have hb' : IsLieBasis v' := (bas _ v' hv hvv').2 (hdet ▸ d.isUnit.map _)
  obtain ⟨th', e₀, -, hle⟩ := GlobalTheory.KeyPow.exists_sec_div P.A.hom (a := algebraMap V K (a⁻¹ : Vˣ)) (b := algebraMap V K a)
    (by rw [← map_mul, Units.inv_mul, map_one]) th
  have hth' : ∀ s : Sp K, ∃ y : P.A.left, P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th' :=
    fun s => (hthne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  refine ⟨⟨P, hP, rig, hrig', th', hth', v', hb'⟩, a, d, ?_, fun κ hκ => ?_⟩
  swap
  · rw [← hdet]
    exact hκ.1 K P hP rig hrig' th hthne v hv th' hth' v' hb' _ _ e₀ hvv'
  have g := (isGen_iff w₁).1 hw₁
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp t.PP.isLB w₁ w' g g' Y.t.PP.isLB P.isLB
  have he'' : eSec P.A ≫ φ' ≫ m.φ = (spMap (algebraMap V K) ≫ yt) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap (algebraMap V K) := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp m.cart
  refine ⟨φ' ≫ m.φ, he'', w'', hn, hq, (isGen_iff w'').2 (T.pgen_comp t.PP.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₁ _ (fun _ => eSec Y.t.G) _ t.PP.rig Y.t.PP.rig yt _
      (rigPull_le m.φ yt he Y.t.PP.L) (fun _ => rfl)).1 hr₁
    have r₁ := (maps_iff w' _ (fun _ => eSec t.G) _ rig t.PP.rig (spMap (algebraMap V K)) _
      (rigPull_le φ' (spMap (algebraMap V K)) he' t.PP.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ rig Y.t.PP.rig (spMap (algebraMap V K) ≫ yt) _
      (rigPull_le (φ' ≫ m.φ) (spMap (algebraMap V K) ≫ yt) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp t.PP.isLB (fun _ => he') r₀ r₁)
  · refine (KeyAtBC.appLE_eq_iff_stalk w'' (KeyAtBC.mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ th').2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart t.PP.isLB (φ' (q y))
    have a₁ := (KeyAtBC.appLE_eq_iff_stalk w₁ (KeyAtBC.mem_of_comm m.cart.1.w hz) M.θ θM).1 (fun j i h =>
      (hth (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))) Z (q ≫ φ') y j i hj hi
    have b₁ := (KeyCancel.appLE_eq_iff_stalk w' θ th).1 hs' Z q y i k hi hk
    have c₁ : gs (q ≫ φ') y _ (θM.f i) = cst ((q ≫ φ') ≫ t.G.hom) y a * gs (q ≫ φ') y _ (θ.f i) := by
      rw [ha i, gs_mul _ y _ hi, gs_constFn _ _ _ y hi]
    have c₂ : gs q y _ (th'.f k) = cst (q ≫ P.A.hom) y (algebraMap V K a) * gs q y _ (th.f k) := by
      rw [e₀ k, gs_mul _ y _ hk, gs_constFn _ _ _ y hk]
    rw [Category.assoc, hp'.1.w, ← Category.assoc, cst_comp] at c₁
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a₁, c₁, b₁, c₂, Units.val_mul]
    ring
  · have e := (GlobalTheory.lieComb_baseChange V K (algebraMap V K) t.G P.A φ' hp' P.g w (vM (i.cast hn)) (Mat i) v (v' i)
      (fun j => (hv' j).trans (by rw [hF]; rfl)) (hMat i)).2 (hvv' i)
    rw [← Category.assoc, e, Category.assoc, hvM, FlagMod.ev_spMap _ yt M.U hz, FlagMod.dualMap_comp,
      KeyAtBC.spMap_comp₀, Category.assoc]
    rfl

end GlobalTheory.KeyFramePoint
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} {n m : ℕ}
    (h : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (m + n) := by
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem squareWeil₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (alpha G t i j) (alpha G t i j / beta G i j) om := by
  intro D T L sc G μ₀ hL t i j _hst B hB X Y r s r' s' hX hY Mo hMo
  have hα : GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j) := by
    have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  have hβ : GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j) := by
    have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
  have pα := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rα
  have pβ := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rβ
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo _ _ hα (isHecke_div hα hβ) pα (resEtaPow_div pα pβ)

end GlobalTheory.FunObj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.WeilTripleW

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') := by
  refine ⟨h.1.div' h'.1, fun x => ?_⟩
  simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_one]

theorem resEtaPow_div {R E : Type} [CommRing R] [CommRing E] [Algebra R E] {K : Subgroup Rˣ}
    {χ χ' : Eˣ →* Circle} {n m : ℕ} (h : GlobalTheory.WeilM.ResEtaPow K χ n) (h' : GlobalTheory.WeilM.ResEtaPow K χ' m) :
    GlobalTheory.WeilM.ResEtaPow K (χ / χ') (n + m) := by
  intro a
  have e1 := h a
  have e2 := h' a
  simp only [MonoidHom.div_apply, Circle.coe_div] at *
  rw [e1, e2]
  split_ifs
  · simp
  · have hm : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    rw [div_eq_iff (by simp), pow_add, mul_assoc, hm, mul_one]

end GlobalTheory.WeilTripleW

theorem GlobalTheory.WeilTripleW.exists_isWeil : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (beta G i j) (beta G i j / alpha G t i j) om := by
  intro D T L sc G μ₀ hL t i j hS B hB X Y r s r' s' hX hY Mo hMo
  obtain ⟨hb, ha, rb, ra⟩ := GlobalTheory.SquareChars.square_chars hL t i j hS
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo
    (beta G i j) (beta G i j / alpha G t i j) hb (GlobalTheory.WeilTripleW.isHecke_div hb ha) rb
    (GlobalTheory.WeilTripleW.resEtaPow_div rb ra)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.CompModel

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem stalkPt_genStr (C : FlagCpt Z e) (z : C.Y.X) (φ : c.F →+* C.Y.X.presheaf.stalk z)
    (hφ : constF e C.Y = (algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField).comp φ) :
    stalkPt C.Y z ≫ C.π ≫ genStr Z = spMap φ := by
  let ρ : c.F →+* C.Y.X.presheaf.stalk z := (Spec.preimage (stalkPt C.Y z ≫ C.π ≫ genStr Z)).hom
  have h0 : spMap ρ = stalkPt C.Y z ≫ C.π ≫ genStr Z := Spec.map_preimage _
  let j := algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField
  letI := (constF e C.Y).toAlgebra
  have hgen : spMap j ≫ stalkPt C.Y z = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have h1 : spMap (j.comp ρ) = spMap (constF e C.Y) := by
    rw [← sp_comp, h0, ← Category.assoc, ← Category.assoc, hgen]
    exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _)))
  have h2 : j.comp ρ = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : ρ = φ := RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk z) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hφ r))
  rw [← h0, h3]

theorem exists_flagPt (C : FlagCpt Z e) {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) :
    ∃ y : FlagPt Z K, p ≫ C.π = y.y ∧ C.Carries p y.frame := by
  obtain ⟨φ, f, t, hT, -⟩ := C.gr_spec (below p)
  let ψ : C.Y.X.presheaf.stalk (below p) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hp : p = spMap ψ ≫ stalkPt C.Y (below p) := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  have hx : spMap ψ ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z = (p ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, ← hp, Category.assoc]
  obtain ⟨g, hg⟩ : ∃ g : EigFrame Z (ψ.comp φ) ((p ≫ C.π) ≫ genι Z), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i := by
    rw [← hx]
    exact EigFrame.exists_baseChange E H Dw l Xo c O β Z _ _ φ _ f ψ
  have ho : (p ≫ C.π) ≫ genStr Z = spMap (ψ.comp φ) := by
    rw [← sp_comp, ← stalkPt_genStr C _ φ hT.2.1, ← Category.assoc (spMap ψ), ← hp, Category.assoc]
  refine ⟨⟨ψ.comp φ, p ≫ C.π, ho, g.v, g.tan, g.eig, g.basis⟩, rfl, below p, ψ, φ, f, t, 1, hp, hT, hx.symm, rfl,
    fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  change IsCombAtG Z.t ((p ≫ C.π) ≫ genι Z)
    (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (Pi.single i 1) (g.v τ i)
  rw [show (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) = g.v τ from funext fun k => (hg τ k).symm]
  exact isCombAtG_single Z.t _ (g.tan τ) i

end Free

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : TrueGeo.Model Y)

end Model

end GlobalTheory.Mean4O.CompModel
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.AffinePointLift

theorem specMap_fromSpec_appLE {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (g : Γ(X, U) ⟶ R) (h : ⊤ ≤ (Spec.map g ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom = g := by
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e0 : hU.fromSpec.appLE U ⊤ h0 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have e : (Spec.map g ≫ hU.fromSpec).appLE U ⊤ h = hU.fromSpec.appLE U ⊤ h0 ≫ (Spec.map g).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, e0, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem specMap_appLE_fromSpec {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{0}}
    (ξ : Spec R ⟶ X) (h : ⊤ ≤ ξ ⁻¹ᵁ U) :
    Spec.map (ξ.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom) ≫ hU.fromSpec = ξ := by
  rw [Spec.map_comp, Category.assoc, hU.SpecMap_appLE_fromSpec ξ (isAffineOpen_top _), IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem exists_lift : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsAffineHom π], ∀ (U : Z.affineOpens) (V V' : Type) [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (ξ : Sp V ⟶ Z) (hξ : ⊤ ≤ ξ ⁻¹ᵁ U.1) (f : V →+* V')
    (ρ : Γ(Y, π ⁻¹ᵁ U.1) →+* V'),
    ρ.comp (π.app U.1).hom = f.comp (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom).hom →
    ∃ ψ : Sp V' ⟶ Y, ψ ≫ π = spMap f ≫ ξ ∧
      ∀ I : Y.IdealSheafData, idlAlong I ψ = (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map ρ := by
  intro Y Z π _ U V V' _ _ _ _ ξ hξ f ρ h
  have hW : IsAffineOpen (π ⁻¹ᵁ U.1) := U.2.preimage π
  let g : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' := CommRingCat.ofHom ρ
  refine ⟨Spec.map g ≫ hW.fromSpec, ?_, fun I => ?_⟩
  · have e : π.appLE U.1 (π ⁻¹ᵁ U.1) le_rfl ≫ g =
        (ξ.appLE U.1 ⊤ hξ ≫ (Scheme.ΓSpecIso (.of V)).hom) ≫ CommRingCat.ofHom f := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact CommRingCat.hom_ext h
    rw [Category.assoc, ← U.2.SpecMap_appLE_fromSpec π hW le_rfl, ← Spec.map_comp_assoc, e, Spec.map_comp,
      Category.assoc, specMap_appLE_fromSpec U.2 ξ hξ]
  · have hle : ⊤ ≤ (Spec.map g ≫ hW.fromSpec) ⁻¹ᵁ (π ⁻¹ᵁ U.1) :=
      fun q _ => hW.fromSpec_preimage_self.ge (x := Spec.map g q) trivial
    rw [GlobalTheory.TraitOrder.idlAlong_eq_map I _ ⟨π ⁻¹ᵁ U.1, hW⟩ hle]
    exact congrArg (fun k : Γ(Y, π ⁻¹ᵁ U.1) ⟶ CommRingCat.of V' => Ideal.map k.hom _)
      (specMap_fromSpec_appLE hW g hle)

end GlobalTheory.AffinePointLift
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

theorem _root_.GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  first | exact @GlobalTheory.CompHS.ChartBd.exists_chart_bd | exact GlobalTheory.CompHS.ChartBd.exists_chart_bd | (intros; apply GlobalTheory.CompHS.ChartBd.exists_chart_bd <;> assumption)
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
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal


theorem _root_.GlobalTheory.T.value_weightSection_flagSpace_eq_rule_at_framedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  first | exact @GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | exact GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR | (intros; apply GlobalTheory.CompHS.BridgeValue.val_sec₀_eq_evR <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem mem_basicOpen_of_sub_one_mem_baseIdeal (R : Type) [CommRing R] (I : Ideal R) (Z : Scheme.{0})
    (p : Z ⟶ Spec (CommRingCat.of R)) (V : Z.Opens) (hV : IsAffineOpen V) (r : Γ(Z, V)) (z : Z)
    (hz : z ∈ V) (hI : I ≤ (p z).asIdeal) (hr : r - 1 ∈ (baseIdeal p I).ideal ⟨V, hV⟩) :
    z ∈ Z.basicOpen r := by
  have hs : z ∈ (baseIdeal p I).support := (mem_support_baseIdeal p I z).2 hI
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hz] at hs
  have h1 : z ∉ Z.basicOpen (r - 1) := by
    rw [Scheme.mem_zeroLocus_iff] at hs
    exact hs _ hr
  rw [Scheme.mem_basicOpen _ _ _ hz] at h1 ⊢
  have hsum : Z.presheaf.germ V z hz r + (-(Z.presheaf.germ V z hz (r - 1))) = 1 := by
    simp [map_sub]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact h
  · exact absurd (by simpa using h.neg) h1

end GlobalTheory.FormalAlg
end
