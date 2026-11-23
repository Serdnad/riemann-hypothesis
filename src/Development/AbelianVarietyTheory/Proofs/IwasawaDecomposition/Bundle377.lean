module

public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
public import Formalism.LocalToGlobal.HermitianForms.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle094
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle353
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle354
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle004
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.Lv

section Build
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp [reL, reV, LinearEquiv.funCongrLeft, LinearMap.funLeft]

theorem reGL_rfl_map {a : ℕ} {R : Type} [CommRing R] (U : Subgroup (GL (Fin a) R)) :
    U.map (reGL (rfl : a = a) R).toMonoidHom = U := by
  have : ∀ x, reGL (rfl : a = a) R x = x := fun x => by
    ext i j
    simp [reGL]
  ext x
  simp [Subgroup.mem_map, this]

theorem exists_herm_level (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (gp : Fin 2 → ℕ) (T f : ℕ)
    {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (K : StepLevel F E hc.sig J T f bad)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → v ∉ bad)
    (hg : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → ∀ x ∈ levelVL hc.sig J v K.Lb,
      (∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z) → x ∈ K.Uloc v)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ K.Uloc v ↔ x ∈ levelVL hc.sig J v K.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J K.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb) :
    ∃ L : Formalism.L2.Herm.StepLevel hc S gp T f, K.Lb = reL h L.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  have hJ' : J = S.gram := by rw [hJ]; ext a b; simp
  subst hJ'
  clear hJ
  refine ⟨{ Lb := K.Lb, Lb_fin := K.Lb_fin, Lb_span := K.Lb_span, Lb_int := fun x hx => Submodule.subset_span (K.Lb_int x hx),
            Lb_dual := ?_, Lb_index := K.Lb_index, Uloc := K.Uloc, Uloc_lev := K.Uloc_lev, Uloc_hyp := ?_, Uloc_g := ?_, UlocAlt := ?_,
            U := K.U, U_eq := K.U_eq }, ?_, ?_, ?_⟩
  · intro y hy
    unfold Formalism.L2.Herm.dualL at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact K.Lb_dual y hy
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  · intro v h0 h1 h2
    exact K.Uloc_hyp v (hbad v h0 h1) h2
  · intro a v h x hx
    exact hg a v h x hx.1 hx.2
  · intro v h x
    exact hT v h x
  · exact (reL_rfl _).symm
  · intro v; exact (reGL_rfl_map _).symm
  · exact (reGL_rfl_map _).symm

end Build
end GlobalTheory.Mem.Col2.Lv

namespace GlobalTheory.Mem.Col2.Lv
section W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uloc_T_iff (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (p q : 𝓞 E) (hq : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T.Prime) (hL : S.Lb = rll_dLat n ((p : E)⁻¹))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hunif : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ x ∈ levelVL σ J v S.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  subst hJ
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hp0 : (p : E) ≠ 0 := fun h => hT0 (by rw [← hpq, h, zero_mul])
  refine ⟨fun hx => ⟨S.Uloc_lev v hx, GlobalTheory.T.level_acts_trivially_on_discriminant_group σ hσ S p q hq hpq hT.ne_zero hL ?_ v hv ?_ x hx⟩, fun h => GlobalTheory.uloc_of_triv_disc σ S v hv x h.1 h.2⟩
  · rw [hL]; exact GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq
  · intro m hm d c hd hc
    exact GlobalTheory.T.unitaryScalar_eq_one_mod_of_fixes_simple_module σ hdeg hσ hfix hun v T hT hunif (S.fM v hv) (S.fM_card v hv) m hm d c hd hc

end W

theorem baseL_eq (B : Base) (n : ℕ) [NeZero n] (t : 𝓞 B.host.E) (ht : (t : B.host.E) ≠ 0) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (h : ∀ x, x ∈ L ↔ x ∈ baseL B n t) : L = rll_dLat n ((t : B.host.E)⁻¹) := by
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := by
    intro j
    have := NeZero.pos n
    constructor
    · intro e; apply Fin.ext; simp [lastIdx]; omega
    · intro e; rw [e]; simp [lastIdx]; omega
  ext x
  rw [h, rll_mem_dLat]
  constructor
  · intro hx
    refine ⟨fun i _ => ?_, ?_⟩
    · obtain ⟨r, e, -⟩ := hx i
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e, hd⟩ := hx (lastIdx n)
      obtain ⟨c, rfl⟩ := hd ((hlast _).2 rfl)
      refine ⟨c, ?_⟩
      rw [e]
      show _ = _ * algebraMap (𝓞 B.host.E) B.host.E (t * c)
      rw [map_mul]
      exact (inv_mul_cancel_left₀ ht _).symm
  · rintro ⟨h1, c, hc⟩ j
    by_cases hj : j = lastIdx n
    · subst hj
      refine ⟨t * c, ?_, fun _ => dvd_mul_right _ _⟩
      have e : x (lastIdx n) = (t : B.host.E) * (c : B.host.E) := by
        have : algebraMap (𝓞 B.host.E) B.host.E c = (t : B.host.E)⁻¹ * x (lastIdx n) := hc
        show _ = _
        rw [show (c : B.host.E) = algebraMap (𝓞 B.host.E) B.host.E c from rfl, this, mul_inv_cancel_left₀ ht]
      rw [e]; rfl
    · obtain ⟨r, hr⟩ := h1 j hj
      exact ⟨r, hr.symm, fun e => absurd ((hlast j).1 e) hj⟩

end GlobalTheory.Mem.Col2.Lv



theorem GlobalTheory.Mem.Col2.TC.level_of_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch chOf F hF i hi cl stab _ lat K Hs lam hG hLb
  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : K.lev.Lb = rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 K.lev.Lb ?_
    rw [hF.piU]; exact hLb
  refine GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (I.rec7 l Z).host.g _ _ rfl K.lev ?_ ?_ ?_
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ K.lev F.gl hG a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram K.lev F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLevelShrink

theorem isCompact_of_isOpen_subgroupOf {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H U A : Subgroup G) (hAU : A ≤ U) (hUH : U ≤ H) (hU : IsCompact (U : Set G))
    (hA : IsOpen {x : H | (x : G) ∈ A}) : IsCompact (A : Set G) := by
  haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)
  have hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ hA
  have hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H) := by
    rw [Subtype.isCompact_iff]
    convert hU using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUH hx⟩, hx, rfl⟩
  have h2 := hU'.inter_right hcl
  rw [Subtype.isCompact_iff] at h2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy

end GlobalTheory.StepLevelShrink

namespace GlobalTheory.StepLevelShrink

theorem exists_stepLevel_shrink : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  intro F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ
  classical
  have hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) y ∈ S.Uloc v :=
    fun y hy => (S.U_eq y).1 hy
  let L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v
      Uloc_le := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_le v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_le v
      Uloc_lev := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_lev v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_lev v
      Uloc_hyp := by
        intro v hv hT
        have hb : v ∉ bad := fun h => hv (Or.inl h)
        have hq : v ∉ Qv := fun h => hv (Or.inr (Finset.mem_coe.2 h))
        simp only [if_neg hq]
        exact S.Uloc_hyp v hb hT
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        have hq : v ∉ Qv := fun hq => hQT v hq h
        simp only [if_neg hq]
        exact S.UlocAlt v h
      U := A
      U_eq := by
        intro x
        constructor
        · intro hx
          refine ⟨(hSU x (hAU hx)).1, fun v => ?_⟩
          by_cases hq : v ∈ Qv
          · simp only [if_pos hq]
            exact ⟨x, hx, rfl⟩
          · simp only [if_neg hq]
            exact (hSU x (hAU hx)).2 v
        · rintro ⟨hP, hv⟩
          have hxS : x ∈ S.U := by
            refine (S.U_eq x).2 ⟨hP, fun v => ?_⟩
            have h1 := hv v
            by_cases hq : v ∈ Qv
            · simp only [if_pos hq] at h1
              obtain ⟨y, hy, hyx⟩ := h1
              rw [← hyx]
              exact (hSU y (hAU hy)).2 v
            · simp only [if_neg hq] at h1
              exact h1
          refine hloc x hxS fun v hq => ?_
          have h1 := hv v
          simp only [if_pos hq] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          exact ⟨y, hy, hyx.symm⟩
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
        haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
        let c : (FiniteAdeleRing (𝓞 F) F ⊗[F] E) →ₗ[FiniteAdeleRing (𝓞 F) F]
            (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          { toFun := TensorProduct.comm F _ _
            map_add' := map_add _
            map_smul' := by
              intro a x
              induction x using TensorProduct.induction_on with
              | zero => simp
              | tmul b e =>
                simp only [TensorProduct.smul_tmul', TensorProduct.comm_tmul, RingHom.id_apply]
                change e ⊗ₜ[F] (a * b) = ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] b)
                rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
              | add x y hx hy => simp [smul_add, hx, hy] }
        haveI : Module.Finite (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          Module.Finite.of_surjective c (TensorProduct.comm F _ _).surjective
        haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
        haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
          IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
        exact isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU
          (fun y hy => (hSU y hy).1) S.U_compact hopen
      U_open := hopen
      chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ
      chi_triv := by
        intro x hx
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply,
          S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)),
          hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }
  refine ⟨L, rfl, rfl, fun v hv => by
    show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v
    exact if_neg hv, ?_⟩
  intro x x' x'' h1 h2
  show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''
  have e1 : Subgroup.inclusion hAU x = x' := Subtype.ext h1
  have e2 : x = x'' := Subtype.ext h2
  rw [e1, e2]

end GlobalTheory.StepLevelShrink
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

theorem _root_.GlobalTheory.T.localBasis_change_integral_unit_det : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  first | exact @GlobalTheory.LocBasisChange.basis_change | exact GlobalTheory.LocBasisChange.basis_change | (intros; apply GlobalTheory.LocBasisChange.basis_change <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianClassCondition_of_chartClasses : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  first | exact @GlobalTheory.HermTransport.classTie_of_chart | exact GlobalTheory.HermTransport.classTie_of_chart | (intros; apply GlobalTheory.HermTransport.classTie_of_chart <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
namespace GlobalTheory.CoefDim


open Classical in
theorem finrank_piTensorProduct {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] : Module.finrank ℂ (⨂[ℂ] i, E i) = ∏ i, Module.finrank ℂ (E i) := by
  let b := Basis.piTensorProduct (fun i => Module.finBasis ℂ (E i))
  rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
  simp [Fintype.card_fin]

theorem finrank_coef_eq_prod : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Module.finrank ℂ R.cX.W = ∏ τ, Module.finrank ℂ (R.MX.H τ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB
  have hp := GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) R.MX
  have hb := GlobalTheory.DefiniteMult.pair_bijective hB.models.inf hp hB.models.cX hB.models.prX
  have m := GlobalTheory.DefLift.AllPlus.finite_smooth_irreducible D _ _ R.MX hp
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.H τ) := fun τ => (m τ).1
  haveI : ∀ τ, FiniteDimensional ℂ (R.MX.sm τ) := fun τ => inferInstance
  have hsm : ∀ τ, Module.finrank ℂ (R.MX.sm τ) = Module.finrank ℂ (R.MX.H τ) := fun τ => by
    rw [(m τ).2.1, finrank_top]
  have e : R.cX.W ≃ₗ[ℂ] Module.Dual ℂ (SmT R.MX) := LinearEquiv.ofBijective R.prX hb
  have hT : Module.finrank ℂ (SmT R.MX) = ∏ τ, Module.finrank ℂ (R.MX.H τ) :=
    (finrank_piTensorProduct (fun τ => R.MX.sm τ)).trans (Finset.prod_congr rfl fun τ _ => hsm τ)
  haveI : FiniteDimensional ℂ (SmT R.MX) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun τ => Module.finBasis ℂ (R.MX.sm τ)))
  rw [e.finrank_eq, Subspace.dual_finrank_eq, hT]

end GlobalTheory.CoefDim
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteMult

theorem topMult_and_extV_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Formalism.IndefR.RecTie.TopMultH R ∧ ∀ i t, Function.Injective (R.extV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h
  refine ⟨?_, fun i t => extV_injective R h.models.HV i t⟩
  intro t
  exact range_top R h.models.inf h.models.cX h.models.prX h.models.HX t

end GlobalTheory.DefiniteMult
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_polynomial_frame_maps_bounded : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  first | exact @GlobalTheory.Mem.UnitPairing.exists_unit_vectors | exact GlobalTheory.Mem.UnitPairing.exists_unit_vectors | (intros; apply GlobalTheory.Mem.UnitPairing.exists_unit_vectors <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.definiteThetaIntegral_integrable_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → (∀ g, IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν) ∧ Continuous (Lift.liftInt ν 𝓕 (thetaKO ω) s F) := by
  first | exact @GlobalTheory.DefLiftCont.theta_integral_integrable_continuous | exact GlobalTheory.DefLiftCont.theta_integral_integrable_continuous | (intros; apply GlobalTheory.DefLiftCont.theta_integral_integrable_continuous <;> assumption)
end
