module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SingleMemIntVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1103
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle032
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.VB

section Generic

variable {X : Scheme.{0}} [IsIntegral X]

theorem genRank_twist {F : X.Modules} {M : LB X} (hM : M.IsLB) :
    genRank (twist F M) = genRank F :=
  have ⟨e⟩ := Twist.nonempty_stalkEquiv (F := F) hM (genericPoint X)
  e.finrank_eq

theorem exists_germ_ne_zero {F : X.Modules} (h : QCoh.IsGloballyGenerated F)
    (hr : genRank F ≠ 0) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := by
  obtain ⟨n, s, hs⟩ := QCoh.isGloballyGenerated_iff_spanStalks.1 h
  by_contra! H
  have : Subsingleton (genStalk F) := subsingleton_of_forall_eq 0 fun t => by
    have ht := (hs (genericPoint X)).ge (Submodule.mem_top (x := t))
    have e : (Set.range fun i => ((F.presheaf.germ ⊤ (genericPoint X) trivial (s i) :
        (F.presheaf.stalk (genericPoint X) :)))) ⊆ {0} := by
      rintro _ ⟨i, rfl⟩
      exact H _
    simpa using Submodule.span_mono e ht
  exact hr Module.finrank_zero_of_subsingleton

theorem mono_sectionHom {F : X.Modules} (s : Γ(F, ⊤))
    (hs : F.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0) : Mono (QCoh.sectionHom s) := by
  refine QCoh.mono_of_locally_app_injective _ fun W x hx => ⟨W, hx, le_rfl, fun a b e => ?_⟩
  have hη := genericPoint_mem hx
  apply (QCoh.structureModuleSectionsEquiv W).injective
  have e' : (QCoh.structureModuleSectionsEquiv W a - QCoh.structureModuleSectionsEquiv W b) •
      Twist.resM F (le_top : W ≤ ⊤) s = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact e
  have e'' := congrArg (F.presheaf.germ W _ hη) e'
  rw [QCoh.germ_smul, Twist.germ_resM, map_zero] at e''
  have := (smul_eq_zero.1 e'').resolve_right hs
  exact sub_eq_zero.1 (germ_injective_of_isIntegral X _ hη (this.trans (map_zero _).symm))

end Generic

variable {κ : Type} [Field κ] {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)]

theorem interNum_one_of_genRank_eq (hp : IsProjOver (strHom κ (X := Z))) (hd : topologicalKrullDim Z = 1)
    {N : LB Z} (hN : N.IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G ![N] = r * interNum κ (structureModule Z) ![N] := by
  have hf := algebraMap_eq_strHom κ Z
  have hL := isLB_vecOne hN
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 : QCoh.suppDim G ≤ 0 := suppDim_le_zero hd h
    have : QCoh.suppDim G < Fintype.card (Fin 1) := h0.trans_lt (by simp)
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) ![N] = interNum κ G ![N] :=
      (diffVanish_chiPic_of_isProjOver (d := 1) hf G hp
        ((QCoh.suppDim_le G).trans_eq (by rw [hd]; rfl))).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_one_eq_genRank_mul : ∀ (κ : Type) [Field κ] (Z : Scheme.{0}) [IsIntegral Z]
    [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ (X := Z)) → topologicalKrullDim Z = 1 →
    ∀ (G : Z.Modules) [GlobalTheory.QCoh.IsFiniteQC G] (N : LB Z), N.IsLB →
      interNum κ G ![N] = (GlobalTheory.VB.genRank G : ℤ) * interNum κ (structureModule Z) ![N] :=
  fun _ _ _ _ _ hp hd G _ _ hN => interNum_one_of_genRank_eq hp hd hN _ G rfl

end GlobalTheory.VB
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate ComplexOrder Matrix

namespace GlobalTheory.Member.LatData

open GlobalTheory.Up.Definite GlobalTheory.LatFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem exists_int_mul_isIntegral_of_fg (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : Λ.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ Λ, ∀ a, IsIntegral ℤ ((d : E) * x a) := by
  classical
  obtain ⟨s, rfl⟩ := hΛ
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (s.biUnion fun x => Finset.univ.image x)
  refine ⟨d, hd, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    intro a
    have h := hint (x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩)
    rwa [zsmul_eq_mul] at h
  | zero => intro a; simpa using isIntegral_zero
  | add x y _ _ hx hy => intro a; simpa [mul_add] using (hx a).add (hy a)
  | smul k x _ hx =>
    intro a
    have h : (d : E) * (k • x) a = algebraMap (𝓞 E) E k * ((d : E) * x a) := by
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
    rw [h]
    exact (RingOfIntegers.isIntegral_coe k).mul (hx a)

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem exists_int_smul_single_mem_of_span_eq_univ (Λ : Submodule (𝓞 E) (Fin r → E))
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ c : ℤ, c ≠ 0 ∧ ∀ b : Fin r, (c : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := by
  classical
  have hmem : ∀ b : Fin r, (Pi.single b 1 : Fin r → E) ∈ Submodule.span E (Λ : Set (Fin r → E)) :=
    fun b => hspan ▸ Submodule.mem_top
  choose f t ht _ hsum using fun b => Submodule.mem_span_iff_exists_finset_subset.1 (hmem b)
  obtain ⟨c, hc, hcint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.biUnion fun b => (t b).image (f b))
  refine ⟨c, hc, fun b => ?_⟩
  have key : ∀ v ∈ t b, (c : E) • (f b v • v) ∈ Λ := by
    intro v hv
    have hI : IsIntegral ℤ ((c : E) * f b v) := by
      have h := hcint (f b v) (Finset.mem_biUnion.2 ⟨b, Finset.mem_univ _, Finset.mem_image_of_mem _ hv⟩)
      rwa [zsmul_eq_mul] at h
    have h : (c : E) • (f b v • v) = (⟨_, hI⟩ : 𝓞 E) • v := by
      rw [smul_smul]
      rfl
    rw [h]
    exact Λ.smul_mem _ (ht b hv)
  rw [← hsum b, Finset.smul_sum]
  exact Λ.sum_mem key

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem cc_intCast' (n : ℤ) : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (n : E) = n := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_cc, map_intCast, map_intCast]

open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [IsCMField E] in
private theorem finite_GL_of_integral_bounded_scaled_entries (c : E) (hc : c ≠ 0) (B : ℝ) :
    {γ : GL (Fin r) E | ∀ a b, IsIntegral ℤ (c * (γ : Matrix (Fin r) (Fin r) E) a b) ∧
      ∀ φ : E →+* ℂ, ‖φ (c * (γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ B}.Finite := by
  have hT := Embeddings.finite_of_norm_le E ℂ B
  have hpi : (Set.univ.pi fun _ : Fin r => Set.univ.pi fun _ : Fin r =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hT
  have hinj : Function.Injective fun γ : GL (Fin r) E => fun a b => c * (γ : Matrix (Fin r) (Fin r) E) a b := by
    intro γ δ h
    ext a b
    exact mul_left_cancel₀ hc (congrFun (congrFun h a) b)
  refine (hpi.preimage hinj.injOn).subset fun γ hγ => ?_
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]
  exact fun a b => hγ a b


open NumberField in
open scoped ComplexConjugate ComplexOrder Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Member.LatData.exists_data_lattice : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ)
    (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
    ∃ X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, X.Λ = Λ := by
  intro E _ _ _ r Λ hfg hspan
  obtain ⟨d, hd, hdint⟩ := exists_int_mul_isIntegral_of_fg Λ hfg
  obtain ⟨c, hc, hcmem⟩ := exists_int_smul_single_mem_of_span_eq_univ Λ hspan
  have hdc : ((d * c : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hd hc
  refine ⟨{ _root_.GlobalTheory.Up.Definite.data (E := E) (r := r) with
    Λ := Λ
    Λ_fg := hfg
    Λ_span := hspan
    den := (d : 𝓞 E) * (d : 𝓞 E)
    den_ne := by exact_mod_cast mul_ne_zero hd hd
    Λ_int := ?_
    Γ_stab := ?_
    Γ_index := ?_
    transv := by
      intro ξ _ hiso s _ _
      change _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ξ ξ = 0 at hiso
      obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h1 := congrArg φ hiso
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, map_zero, Complex.ofReal_eq_zero,
        Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _] at h1
      have hξ : ∀ a, ξ a = 0 := fun a => by simpa using h1 a (Finset.mem_univ a)
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      ext a b
      simp [_root_.GlobalTheory.Up.Definite.data, _root_.ReciprocityTheory.ChartRestriction.G.FD.transvMat, hξ, Matrix.one_apply] }, rfl⟩
  · intro x hx y hy
    show IsIntegral ℤ ((((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) x y)
    rw [_root_.GlobalTheory.Up.Definite.herm_one, Finset.mul_sum]
    refine IsIntegral.sum _ fun a _ => ?_
    have h : (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) * (x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a)) =
        ((d : E) * x a) * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((d : E) * y a) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.cc_mul, cc_intCast',
        show (((d : 𝓞 E) * (d : 𝓞 E) : 𝓞 E) : E) = (d : E) * (d : E) by simp]
      ring
    rw [h]
    exact (hdint x hx a).mul (_root_.ReciprocityTheory.ChartRestriction.G.FD.isIntegral_cc (hdint y hy a))
  · intro γ hγ
    change γ ∈ (⊥ : Subgroup (GL (Fin r) E)) at hγ
    rw [Subgroup.mem_bot] at hγ
    subst hγ
    simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab]
  · refine ⟨(finite_GL_of_integral_bounded_scaled_entries ((d * c : ℤ) : E) hdc ‖((d * c : ℤ) : ℂ)‖).toFinset,
      fun γ hγ => ⟨γ, ?_, by simp⟩⟩
    rw [Set.Finite.mem_toFinset]
    intro a b
    have hcol : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (Pi.single b 1) =
        fun a => (γ : Matrix (Fin r) (Fin r) E) a b := by
      ext a; simp
    have hnorm : ∀ φ : E →+* ℂ, ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 1 := by
      intro φ
      have h0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1)
          ((γ : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single b 1) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (1 : Matrix (Fin r) (Fin r) E) (Pi.single b 1) (Pi.single b 1) := hγ.1 _ _
      have h1 := congrArg φ h0
      rw [_root_.GlobalTheory.Up.Definite.map_herm_one_self, _root_.GlobalTheory.Up.Definite.map_herm_one_self, hcol] at h1
      have h2 : ∑ a, ‖φ ((Pi.single b 1 : Fin r → E) a)‖ ^ 2 = 1 := by
        rw [Finset.sum_eq_single b] <;> simp +contextual
      have h3 := Complex.ofReal_injective h1
      rw [h2] at h3
      have h4 := Finset.single_le_sum (f := fun a => ‖φ ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      rw [h3] at h4
      nlinarith [norm_nonneg (φ ((γ : Matrix (Fin r) (Fin r) E) a b))]
    refine ⟨?_, fun φ => ?_⟩
    · have hmemγ := (hγ.2 _).mp (hcmem b)
      have hi := hdint _ hmemγ a
      rw [Matrix.mulVec_smul, hcol] at hi
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      have h : ((d * c : ℤ) : E) * (γ : Matrix (Fin r) (Fin r) E) a b =
          (d : E) * ((c : E) * (γ : Matrix (Fin r) (Fin r) E) a b) := by
        push_cast
        ring
      rw [h]
      exact hi
    · rw [map_mul, norm_mul, map_intCast]
      exact mul_le_of_le_one_right (norm_nonneg _) (hnorm φ)

end GlobalTheory.Member.LatData
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts GlobalTheory.ProjSpace
open scoped Matrix

namespace GlobalTheory.ProjPos

theorem leviV_log_pos {n N : ℕ} {w : Fin N → V n → ℂ} {x : V n} (hC : ∀ a, ContDiffAt ℂ 2 (w a) x) {j : Fin N}
    (hj : w j =ᶠ[𝓝 x] fun _ => 1) (ξ : V n) (h : ¬ ∀ a, fderiv ℂ (w a) x ξ = 0) :
    0 < (leviV n (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) x ξ.ofLp).re := by
  have hD : ∀ a, DifferentiableAt ℂ (w a) x := fun a => (hC a).differentiableAt (by simp)
  have h1 : w j x = 1 := hj.eq_of_nhds
  have hne : (fun i => w i x) ≠ 0 := fun e => one_ne_zero (h1.symm.trans (congrFun e j))
  have e1 : (fun z => ((Real.log (∑ a, ‖w a z‖ ^ 2) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
  have hJ (a) : (wJac n N w x *ᵥ ξ.ofLp) a = fderiv ℂ (w a) x ξ := by
    have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
      ext i
      simp [bas, Pi.single_apply]
    conv_rhs => rw [hξ]

    simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hD a), map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e1, leviLogNormSq n N w x ξ.ofLp hC hne, Complex.ofReal_re]
  refine div_pos (sqNorm_pos fun hz => h fun a => ?_) (sqNorm_pos hne)
  rw [projPerp_mulVec, sub_eq_zero] at hz
  have h2 := congrFun hz j
  rw [hJ, hj.fderiv_eq, Pi.smul_apply, h1, smul_eq_mul, mul_one] at h2
  have h3 := congrFun hz a
  rw [hJ, ← h2] at h3
  simpa using h3

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {c : AlgChart p σ D} {y : CxPts p σ} {W : Y.Opens} {ξ : V D}


variable (c y ξ) in
def dirDer (f : Γ(Y, W)) : ℂ := fderiv ℂ (ev p σ W f ∘ c.e.symm) (c.e y) ξ

theorem dirDer_add (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f + g) = dirDer c y ξ f + dirDer c y ξ g := by
  have e : ev p σ W (f + g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) + (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_add _ _ _
  simp only [dirDer, e, fderiv_add (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW)]
  rfl

theorem dirDer_mul (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (f g : Γ(Y, W)) :
    dirDer c y ξ (f * g) = ev p σ W f y * dirDer c y ξ g + ev p σ W g y * dirDer c y ξ f := by
  have e : ev p σ W (f * g) ∘ c.e.symm = (ev p σ W f ∘ c.e.symm) * (ev p σ W g ∘ c.e.symm) :=
    funext fun v => ev_mul _ _ _
  simp only [dirDer, e, fderiv_mul (c.differentiableAt_ev f hy hW) (c.differentiableAt_ev g hy hW),
    Function.comp_apply, c.e.left_inv hy]
  rfl

theorem dirDer_const (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) {f : Γ(Y, W)} {a : ℂ}
    (h : ∀ z ∈ ptsIn p σ W, ev p σ W f z = a) : dirDer c y ξ f = 0 := by
  have e : ev p σ W f ∘ c.e.symm =ᶠ[𝓝 (c.e y)] fun _ => a :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W)).mem_nhds (mem_over c.e hy hW)) fun v hv => h _ hv.2
  rw [dirDer, e.fderiv_eq]
  simp

theorem dirDer_res {W' : Y.Opens} (h : W' ≤ W) (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W') (f : Γ(Y, W)) :
    dirDer c y ξ (resG Y h f) = dirDer c y ξ f := by
  have e : ev p σ W' (resG Y h f) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] ev p σ W f ∘ c.e.symm :=
    eventually_of_mem ((isOpen_over c.e (isOpen_ptsIn W')).mem_nhds (mem_over c.e hy hW))
      fun v hv => ev_res h hv.2 _
  simp only [dirDer, e.fderiv_eq]

theorem chartDirectionalDerivativeRegular_coordinate (hy : y ∈ c.e.source) (a : Fin D) : dirDer c y ξ (c.x a) = ξ a := by
  have e : ev p σ _ (c.x a) ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (EuclideanSpace.proj (𝕜 := ℂ) a : V D →L[ℂ] ℂ) :=
    eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy)) fun v hv =>
      (c.apply_eq _ (c.e.map_target hv) a).symm.trans (by rw [c.e.right_inv hv]; rfl)
  rw [dirDer, e.fderiv_eq, ContinuousLinearMap.fderiv]
  rfl

theorem eq_zero_of_dirDer (hy : y ∈ c.e.source) (hW : y ∈ ptsIn p σ W) (hU : IsAffineOpen W)
    (h0 : ∀ f : Γ(Y, W), dirDer c y ξ f = 0) : ξ = 0 := by
  ext b
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := c.U) ⟨_, mem_ptsIn.1 (c.source_subset hy)⟩ (mem_ptsIn.1 hW)
  have hB : y ∈ ptsIn p σ (Y.basicOpen h) := mem_ptsIn.2 hh
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG Y hhW (c.x b))
  have ha' : resG Y hhW (c.x b) * resG Y (Y.basicOpen_le h) (h ^ n) = resG Y (Y.basicOpen_le h) a := by
    rw [map_pow]; exact ha
  have e := congrArg (dirDer c y ξ) ha'
  rw [dirDer_mul hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, dirDer_res _ hy hB, h0, h0, chartDirectionalDerivativeRegular_coordinate hy, mul_zero,
    zero_add, ev_res _ hB, ev_eq hW, map_pow, ← ev_eq] at e
  exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero n ((mem_ptsIn_basicOpen hW h).1 hB))

variable {N : ℕ} (i : Y ⟶ PSpace k N) (hi : i ≫ PSpace.str k N = p)


include hi in
theorem eq_zero_of_dirDer_ratio [IsClosedImmersion i] (hy : y ∈ c.e.source) {j : Fin (N + 1)}
    (hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j)) (h0 : ∀ a, dirDer c y ξ (i.app _ (ratio k N j a)) = 0) : ξ = 0 := by
  refine eq_zero_of_dirDer hy hW ((isAffineOpen_chart k N j).preimage i) fun f => ?_
  obtain ⟨g, rfl⟩ := i.app_surjective _ (isAffineOpen_chart k N j) f
  obtain ⟨P, rfl⟩ := aeval_ratio_surjective k N j g
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine dirDer_const hy hW (a := σ a) fun z hz => ?_
    rw [← ev_of_comp hm, MvPolynomial.aeval_C]
    exact ev_algX ((mem_ptsIn_preimage hm).1 hz) a
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), dirDer_add hy hW, hP, hQ, add_zero]
  | mul_X P a hP => rw [map_mul, map_mul, dirDer_mul hy hW, hP, MvPolynomial.aeval_X, h0, mul_zero, mul_zero, add_zero]

theorem fubiniStudy_weight_pullback_chart_formula (j : Fin (N + 1)) (z : CxPts p σ) :
    ((ProjAn.fsO1 k σ N).pull i hi).φ (fun _ => j) z =
      Real.log (∑ a, ‖ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) z‖ ^ 2) := by
  have hm : ∀ z : CxPts p σ, (PtsOver.map i hi _ z).1 = z.1 ≫ i := fun _ => rfl
  refine (Weight.pull_φ _ _ _ _ _).trans ((Weight.fsBasis_φ _ _ _ _ _ _ _).trans
    (congrArg _ (Finset.sum_congr rfl fun a _ => ?_)))
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← ev_of_comp hm]
  rfl

theorem fubiniStudy_weight_pullback_isSmooth (R : AnRead p σ D) : ((ProjAn.fsO1 k σ N).pull i hi).IsSmooth R :=
  Weight.IsSmooth.pull (R := .all _ σ N) (Weight.isSmooth_fsBasis _ _ _ _ _) i hi R

theorem fubiniStudy_weight_pullback_closed_immersion_strictPos [IsClosedImmersion i] (R : AnRead p σ D) :
    ((ProjAn.fsO1 k σ N).pull i hi).StrictPos R := by
  refine (fubiniStudy_weight_pullback_isSmooth i hi R).strictPos_of_exists fun y => ?_
  obtain ⟨l, hy⟩ := R.cover y
  obtain ⟨j, hj⟩ := exists_mem_chart k N (i (y.1 (IsLocalRing.closedPoint ℂ)))
  have hW : y ∈ ptsIn p σ (i ⁻¹ᵁ chart k N j) := mem_ptsIn.2 hj
  set c := R.chart l
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (i ⁻¹ᵁ chart k N j))
  have hn := ho.mem_nhds (mem_over c.e hy hW)
  refine ⟨c, fun _ => j, hy, mem_ptsIn.2 (Set.mem_iInter.2 fun _ => hj), fun ξ hξ => ?_⟩
  simp only [AlgChart.levi, fubiniStudy_weight_pullback_chart_formula]
  refine leviV_log_pos (w := fun a => ev p σ (i ⁻¹ᵁ chart k N j) (i.app _ (ratio k N j a)) ∘ c.e.symm)
    (fun a => ((contDiffOn_of_differentiableOn D _ _ ho (c.holo _ _)).contDiffAt hn).of_le
      (WithTop.coe_le_coe.2 le_top)) (j := j) (eventually_of_mem hn fun v hv => ?_) (WithLp.toLp 2 ξ) fun h => ?_
  · rw [Function.comp_apply, ratio, ratioOn_self, map_one, ev_eq hv.2, map_one]
  · exact hξ (congrArg WithLp.ofLp (eq_zero_of_dirDer_ratio i hi hy hW h))

end GlobalTheory.ProjPos
end
end
