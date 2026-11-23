module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousChartIsotropicUnipotentRadical
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrOnOfNotFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1336
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.Peel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem globFn_eq (hU : Unr E) {S : Set (Pl E)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1) {w : Pl E} (hw : w ∈ S) (x : finU (E := E) (n := n)) :
    globFn S f x = f w (toSub _ (cLoc w x.1)) * ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1)) := by
  have hfin : (Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u hu ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  conv_lhs => rw [← Set.insert_diff_self_of_mem hw]
  exact finprod_mem_insert' _ (fun h => h.2 rfl) (hfin.subset Set.inter_subset_right)

theorem trOn_hop_peel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) * twTr σ.ρ (KL n w) (K' w) ((K' w : Set (UL n w)).indicator 1) LinearMap.id = twTr σ.ρ (KL n w) (K' w) (f w) LinearMap.id * trOn (π ⊓ fixed (RF E n) (globLev S K')) (hop S K' (Function.update f w ((K' w : Set (UL n w)).indicator 1))) := by
  intro E _ _ _ hU n hn π hπ S hS K' hK' f hf w hw σ hσ
  obtain ⟨e, he⟩ := LocCompU.exists_equiv hU n w
  let ι : UL n w →* finU (E := E) (n := n) := (Subgroup.inclusion (inf_le_left : locU n w ≤ finU (E := E) (n := n))).comp
    e.toMulEquiv.symm.toMonoidHom
  let r : finU (E := E) (n := n) →* UL n w := ((cLoc w).comp (finU (E := E) (n := n)).subtype).codRestrict _ fun x => GlobLev.cLoc_mem_UL w x.1
  have hιw : ∀ h, cLoc w (ι h).1 = h.1 := fun h => by
    change cLoc w ((e.symm h : locU n w) : UA E n) = _
    rw [← he, e.apply_symm_apply]
  have hιu : ∀ h, ∀ u ∈ S, u ≠ w → cLoc u (ι h).1 = 1 := fun h u hu huw => by
    obtain ⟨v, -, hv⟩ := hS w
    exact GlobalTheory.DefU.LocRet.mem_locU_ne (e.symm h).2 fun h' => huw ((hv u ⟨hu, h'⟩).trans (hv w ⟨hw, rfl⟩).symm)
  have hr : ∀ h, r (ι h) = h := fun h => Subtype.ext (hιw h)
  have hc : ∀ x ∈ r.ker, ∀ h, Commute x (ι h) := fun x hx h => by
    have h1 : cLoc w x.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : GlobalTheory.DefU.LocRet.ret w n x.1 = 1 := by
      apply e.injective
      rw [map_one]
      refine Subtype.ext ((he _).trans ?_)
      exact (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl x.1).trans h1
    have h3 := GlobalTheory.DefU.LocRet.commute_ret x.1 (e.symm h)
    rw [h2, OneMemClass.coe_one, inv_one, one_mul] at h3
    exact Subtype.ext h3.eq
  have hK1 : ∀ k ∈ K' w, ι k ∈ globLev S K' := fun k hk => (GlobLev.mem_globLev S K' _).2 fun u hu => by
    by_cases huw : u = w
    · subst huw
      have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = k := Subtype.ext (hιw k)
      rwa [this]
    · have : (⟨cLoc u (ι k).1, GlobLev.cLoc_mem_UL u _⟩ : UL n u) = 1 := Subtype.ext (hιu k u hu huw)
      rw [this]
      exact one_mem _
  have hK2 : ∀ k ∈ globLev S K', r k ∈ K' w := fun k hk => (GlobLev.mem_globLev S K' _).1 hk w hw
  obtain ⟨hind, h0, -⟩ := GlobalTheory.TwTrUnit.twTr_unit E n w (K' w) (hK'.1 w) σ
  set a' : UL n w → ℂ := (K' w : Set (UL n w)).indicator 1 with ha'
  have hf' : IsTest (KL n) K' (Function.update f w a') := by
    refine ⟨fun u => ?_, ?_⟩
    · by_cases huw : u = w
      · subst huw
        rwa [Function.update_self]
      · rw [Function.update_of_ne huw]
        exact hf.1 u
    · filter_upwards [hf.2, (Set.finite_singleton w).compl_mem_cofinite] with u h1 h2
      rwa [Function.update_of_ne h2]
  let b : r.ker → ℂ := fun x => ∏ᶠ u ∈ S \ {w}, f u (toSub _ (cLoc u x.1.1))
  have hsplit : ∀ g : ∀ u : Pl E, UL n u → ℂ, IsTest (KL n) K' g → (∀ u, u ≠ w → g u = f u) →
      ∀ h (x : r.ker), globFn S g (ι h * x) = g w h * b x := fun g hg hgf h x => by
    rw [globFn_eq hU hg.2 hw]
    have h1 : cLoc w x.1.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
    congr 1
    · rw [Subgroup.coe_mul, map_mul, hιw, h1, mul_one, toSub, dite_eq_left h.2]
    · refine finprod_mem_congr rfl fun u hu => ?_
      rw [hgf u hu.2, Subgroup.coe_mul, map_mul, hιu h u hu.1 hu.2, one_mul]
  have hF := hsplit f hf fun _ _ => rfl
  have hF' := hsplit _ hf' fun u hu => Function.update_of_ne hu _ _
  simp only [Function.update_self] at hF'
  have hH := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' f hf
  have hH' := GlobHecke.isHecke_globFn E hU n hn S hS K' hK' _ hf'
  have hb : ∀ x : r.ker, b x = globFn S (Function.update f w a') x := fun x => by
    have := hF' 1 x
    rw [map_one, one_mul, ha', Set.indicator_of_mem (K' w).one_mem, Pi.one_apply, one_mul] at this
    exact this.symm
  have hopen := (GlobLev.globLev_isOpen_isCompact_isLevel E hU n hn S hS K' hK').2.2.1
  have hbfin : {q : r.ker ⧸ (globLev S K').subgroupOf r.ker | b q.out ≠ 0}.Finite := by
    refine Set.Finite.of_finite_image (f := fun q => (((q.out : r.ker) : finU (E := E) (n := n)) : finU (E := E) (n := n) ⧸ globLev S K'))
      ((GlobalTheory.TwTrLin.finite_out_support hopen hH'.1).subset ?_) fun p _ q _ h => ?_
    · rintro _ ⟨q, hq, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') ((q.out : r.ker) : finU (E := E) (n := n))
      change globFn S _ _ ≠ 0
      rw [hk, (hH'.2 _ k.2 _).2, ← hb]
      exact hq
    · have h' : ((((p.out : r.ker) : finU (E := E) (n := n))) : finU (E := E) (n := n) ⧸ globLev S K') = ((q.out : r.ker) : finU (E := E) (n := n)) := h
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      have := QuotientGroup.eq.1 h'
      simpa using this
  haveI := σ.irred
  have hiso : π ≤ LocUniq.isoPart σ.ρ ((RF E n).comp ι) := by
    obtain ⟨p, hp, -, φ, hφ0, hφm, hφ⟩ := hσ
    have hpe : ∀ g, p (e.symm g) = g := fun g => Subtype.ext ((hp _).trans (hιw g))
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let s : UL n w →* UA E n := (finU (E := E) (n := n)).subtype.comp ι
    let Φ : σ.ρ.IntertwiningMap (π'.rep.comp s) :=
      ⟨φ.codRestrict π hφm, fun g => LinearMap.ext fun v => Subtype.ext (by
        have := hφ (e.symm g) v
        rw [hpe] at this
        exact this)⟩
    have hΦ0 : Φ ≠ 0 := fun h =>
      hφ0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨h1, -⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (UL n w) π σ.V σ.V π'.rep s σ.ρ σ.ρ π'.isIrreducible_rep
      σ.irred σ.irred (fun g => ⟨e (GlobalTheory.DefU.LocRet.ret w n g), fun y => by
        have h3 := GlobalTheory.DefU.LocRet.commute_ret g (e.symm y)
        have h4 : s (e (GlobalTheory.DefU.LocRet.ret w n g)) = GlobalTheory.DefU.LocRet.ret w n g := by
          change ((e.symm (e _) : locU n w) : UA E n) = _
          rw [e.symm_apply_apply]
        rw [h4]
        exact h3⟩) Φ hΦ0
    intro v hv
    have hle : (⨆ ψ : σ.ρ.IntertwiningMap (π'.rep.comp s), LinearMap.range ψ.toLinearMap) ≤
        (LocUniq.isoPart σ.ρ ((RF E n).comp ι)).comap π.subtype := by
      refine iSup_le fun ψ => ?_
      rintro _ ⟨u, rfl⟩
      exact Submodule.mem_iSup_of_mem (⟨π.subtype ∘ₗ ψ.toLinearMap, fun g => LinearMap.ext fun y =>
        congrArg Subtype.val (LinearMap.congr_fun (ψ.isIntertwining' g) y)⟩ :
          σ.ρ.IntertwiningMap ((RF E n).comp ι)) ⟨u, rfl⟩
    rw [h1] at hle
    exact hle (Submodule.mem_top : (⟨v, hv⟩ : π) ∈ ⊤)
  exact trOn_levOp_cross ι r hr hc hK1 hK2 (RF E n) π (fun g v hv => hπ.stable _ v hv) σ.ρ hiso _ (KL n w) h0 _ _
    (f w) a' b hF hF' (fun k hk x => (hH.2 k hk x).2) (fun k hk x => (hH'.2 k hk x).2) (hf.1 w).2 hind.2
    (fun k hk x => by
      rw [hb, hb, hb]
      exact hH'.2 _ hk _)
    (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 (hf.1 w).1) (GlobalTheory.TwTrLin.finite_out_support (hK'.1 w).1 hind.1) hbfin

end GlobalTheory.BCT.Peel
end
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
end

section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj


theorem _root_.GlobalTheory.T.exists_continuous_chart_isotropicUnipotentRadical : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∃ φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × GlobalTheory.ResidueEisenstein.ModConj.skewA σ j → GAd σ J, Continuous φ ∧ ∀ b s, GlobalTheory.SphEis.Crd σ J C D Z J₀ (φ (b, s)) b ((s : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) - inclR (F := F) (AF F) (2⁻¹ : E) • (b * GlobalTheory.SphEis.plus σ J₀ b)) := by
  first | exact @GlobalTheory.ResidueEisenstein.ChartU.chart | exact GlobalTheory.ResidueEisenstein.ChartU.chart | (intros; apply GlobalTheory.ResidueEisenstein.ChartU.chart <;> assumption)
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspidal_spectrum_finiteness_of_decay_harishChandra : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → SpecFin := by
  first | exact @GlobalTheory.SpecFinite.specFin | exact GlobalTheory.SpecFinite.specFin | (intros; apply GlobalTheory.SpecFinite.specFin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.real_maps_two_triples_agree : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xa Xb : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) oa oa' ob ob' R,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xa oa oa' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B Γ Xb ob ob' →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ oa oa' R → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsRealMaps B Γ ob ob' R := by
  first | exact @GlobalTheory.RealMapsChars.isRealMaps_of_sameExp | exact GlobalTheory.RealMapsChars.isRealMaps_of_sameExp | (intros; apply GlobalTheory.RealMapsChars.isRealMaps_of_sameExp <;> assumption)
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

theorem _root_.GlobalTheory.T.theta_series_factorizable_restriction : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ w, w ∉ S → φ w = G.M'.vac w) →
    ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')),
    (∀ w, w ∉ S → ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ,
      G.M'.co.rho B.ψ γ (pure f φ) = c • pure f φ → G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∃ (m : ℕ) (f' : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ' : Fin m → ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
      (∀ i w, φ' i w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧ (∀ i w, w ∉ S → φ' i w = G.M'.vac w) ∧
      Ψ = ∑ i, pure (f' i) (φ' i) := by
  first | exact @GlobalTheory.VacFactor.factor | exact GlobalTheory.VacFactor.factor | (intros; apply GlobalTheory.VacFactor.factor <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.adelicGroupAlgebraAction_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Function.Injective (GlobalTheory.LKGeo.actOn L.rep (AfP p)) := by
  exact GlobalTheory.LKGeo.actOn_rep_afP_injective
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_inverse_adeleAwayFromP_of_unitCongruences : ∀ (p : ℕ) [Fact p.Prime] (c : AfP p) (u : ℕ → ℕ), (∀ n : ℕ, 0 < n → n.Coprime p → (u n).Coprime n ∧ ∃ β : AfP p, IsIntAf β ∧ c = (u n : AfP p) + n • β) → ∃ c' : AfP p, c * c' = 1 := by
  first | (exact @GlobalTheory.AfUnit.exists_mul_eq_one) | (exact GlobalTheory.AfUnit.exists_mul_eq_one) | (intros; apply GlobalTheory.AfUnit.exists_mul_eq_one  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem _root_.GlobalTheory.T.exists_ringMaps_lift_vertical_deformations_affine : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (k : X.F.J) (W : M.X.Opens) (hW : IsAffineOpen W)
    (hle : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k), ∃ e : VIx Dw → (Γ(M.X, W) →+* DualNumber Γ(M.X, W)), (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W) →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b : VIx Dw, ∃ w : FrPt Xo c (DualNumber K),
          IsVert Q (Pi.single b.toF (1 : K)) w ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.CompHS.exists_vertLift | exact GlobalTheory.CompHS.exists_vertLift | (intros; apply GlobalTheory.CompHS.exists_vertLift <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

theorem _root_.GlobalTheory.T.eq_zero_of_pairing_vanishes : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (z : AfP p ⊗[ℚ] VQ D), (∀ v, (D.EF.baseChange ℚ).baseChange (AfP p) v z = 0) → z = 0 := by
  first | (exact @GlobalTheory.LKGeo.nondeg_afP) | (exact GlobalTheory.LKGeo.nondeg_afP) | (intros; apply GlobalTheory.LKGeo.nondeg_afP  <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct

theorem _root_.GlobalTheory.T.int_dvd_of_eq_nat_mul_integralAdeleAwayFromP : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 0 < n → n.Coprime p → ∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c := by
  first | (exact @GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (exact GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf) | (intros; apply GlobalTheory.LKGeo.IntDvd.int_dvd_of_eq_mul_isIntAf <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.AfUnitSplit

theorem isInt_add' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_mul' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isInt_intCast' {p : ℕ} (k : ℤ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ k

theorem exists_dvd_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a →
    IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧
      ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  intro p _ a b K hK hKp ha hb hab
  obtain ⟨m₀, β, hβ, e⟩ := LaHatMod.exists_int_add_mul K hK hKp a ha
  have hgpos : 0 < Int.gcd m₀ (K : ℤ) := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hK.ne')
  obtain ⟨g, a₀, K₀, hg, hcop, hm, hKe⟩ := Int.exists_gcd_one' hgpos
  have hgK : g ∣ K := by
    have : (g : ℤ) ∣ (K : ℤ) := ⟨K₀, by rw [hKe]; ring⟩
    exact_mod_cast this
  have hgp : g.Coprime p := Nat.Coprime.coprime_dvd_left hgK hKp
  have hbez : (1 : ℤ) = a₀ * Int.gcdA a₀ K₀ + K₀ * Int.gcdB a₀ K₀ := by
    rw [← Int.gcd_eq_gcd_ab, hcop]; rfl
  set s := Int.gcdA a₀ K₀
  set t := Int.gcdB a₀ K₀
  have hbez' : (1 : AfP p) = (a₀ : AfP p) * s + (K₀ : AfP p) * t := by
    have := congrArg (Int.cast : ℤ → AfP p) hbez; push_cast at this; exact this
  have hKc : (K : AfP p) = (K₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hKe; push_cast at this; exact this
  have hmc : (m₀ : AfP p) = (a₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hm; push_cast at this; exact this
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  set u := algebraMap ℚ (AfP p) (g : ℚ)⁻¹
  have hu : (g : AfP p) * u = 1 := by
    rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hgq, map_one]
  have ha' : a = (g : AfP p) * ((a₀ : AfP p) + (K₀ : AfP p) * β) := by
    rw [e, hmc, hKc]; ring
  have hεb : ((a₀ : AfP p) + (K₀ : AfP p) * β) * b = (K₀ : AfP p) := by
    linear_combination (-(((a₀ : AfP p) + (K₀ : AfP p) * β) * b - (K₀ : AfP p))) * hu + u * hab
      - u * b * ha' + u * hKc
  refine ⟨g, (a₀ : AfP p) + (K₀ : AfP p) * β, (s : AfP p) - b * ((s : AfP p) * β - t), hgp, hgK,
    isInt_add' (isInt_intCast' _) (isInt_mul' (isInt_intCast' _) hβ),
    isInt_sub' (isInt_intCast' _) (isInt_mul' hb (isInt_sub' (isInt_mul' (isInt_intCast' _) hβ) (isInt_intCast' _))),
    ?_, ha'⟩
  linear_combination (-((s : AfP p) * β - t)) * hεb - hbez'

end GlobalTheory.AfUnitSplit
end
