module

public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle157
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GeometricStatement
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle010
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.DualScheme

theorem preDual_of_isPerfect {S : Scheme.{0}} [IsLocallyNoetherian S] {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (h : IsPerfect A B P) :
    PreDual A B P := by
  refine ⟨h.isLB, ?_, ?_, h.ker_right, ?_⟩
  · exact CubeNoeth.isAdditive_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  · exact CubeNoeth.isAdditive_swap_of_triv_axes hA hB h.isLB h.zero_left h.zero_right
  · intro k _ _ t
    exact (Set.finite_singleton (1 : Over.mk t ⟶ A)).subset fun x hx ↦ h.ker_left _ x hx

theorem pull_lam_of_left {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (c : Pic G.left) (u : T'.left ⟶ T.left)
    {a b : T ⟶ G} {a' b' : T' ⟶ G} (ha : u ≫ a.left = a'.left) (hb : u ≫ b.left = b'.left) :
    CechPic.pull u (lam c a b) = lam c a' b' := by
  have hT : u ≫ T.hom = T'.hom := by
    rw [← Over.w a, ← Category.assoc, ha, Over.w a']
  have hab : u ≫ (a * b).left = (a' * b').left := by
    rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, ← Category.assoc]
    congr 1
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_fst, GlobalTheory.AbDual.lift_left_fst, ha]
    · rw [Category.assoc, GlobalTheory.AbDual.lift_left_snd, GlobalTheory.AbDual.lift_left_snd, hb]
  have hu : ∀ X : Over S, (toUnit X).left = X.hom := fun X => by
    simpa using Over.w (toUnit X)
  have h1 : u ≫ (1 : T ⟶ G).left = (1 : T' ⟶ G).left := by
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, ← Category.assoc, hu, hu, hT]
  simp only [GlobalTheory.CechPic.lam, map_add (f := _), map_sub, ← GlobalTheory.CechPic.pull_comp, hab, h1, ha, hb]

theorem pull_lam_sq {S S' : Scheme.{0}} {b : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G b φ) (c : Pic G.left) {l : (G' ⊗ G').left ⟶ (G ⊗ G).left}
    (l₁ : l ≫ (fst G G).left = (fst G' G').left ≫ φ) (l₂ : l ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    CechPic.pull l (lam c (fst G G) (snd G G)) = lam (CechPic.pull φ c) (fst G' G') (snd G' G') := by
  rw [GlobalTheory.CechPic.lam_pull_of_isGrpPullback hp c (fst G' G') (snd G' G')]
  exact pull_lam_of_left (T := G ⊗ G) (T' := Over.mk ((G' ⊗ G').hom ≫ b)) (a := fst G G)
    (b := snd G G) (a' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (fst G' G'))
    (b' := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hp _ (snd G' G')) c l (by rw [l₁]; rfl) (by rw [l₂]; rfl)

theorem ktrivDual : KTrivModel → FinDual → KTrivDual := by
  intro hM hF R _ A _ g hA hg L hL hK
  obtain ⟨R₀, _, σ, A₀, _, φ, L₀, _, hA₀, hg₀, hp, hL₀, hK₀, hiso⟩ := hM R A g hA hg L hL hK
  haveI := hA₀.comm
  have hperf : IsPerfect A₀ A₀ (abelian₂ A₀ L₀) := isPerfect_lam hL₀ hK₀
  have hd : IsDual A₀ A₀ (abelian₂ A₀ L₀) :=
    hF R₀ A₀ A₀ g hA₀ hA₀ hg₀ hg₀ _ (preDual_of_isPerfect hA₀ hA₀ hperf)
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine IsDual.baseChange hp hp l₁ l₂ hP ?_ hd
  refine (cls_eq_iff (pull_isLB hperf.isLB l) hP).1 ?_
  rw [cls_pull hperf.isLB,
    show cls _ hperf.isLB = lam (cls L₀ hL₀) (fst A₀ A₀) (snd A₀ A₀) from cls_cube_two hL₀ _ _ hperf.isLB,
    show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP,
    (cls_eq_iff hL (pull_isLB hL₀ φ)).2 hiso, cls_pull hL₀]
  exact pull_lam_sq hp _ l₁ l₂

end GlobalTheory.CompanionTheory.DualScheme
end
end

section

theorem _root_.GlobalTheory.T.GeometricStatement : CompanionTheory.RgExh.Dec.L.Geo :=
  GlobalTheory.CompanionTheory.UGeo.geo
end

section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}

def evalHom (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (u : X) : homIn δ ρ ⊤ →ₗ[ℂ] H where
  toFun T := T.1 u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_evalHom (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) (y : X)
    (T : homIn δ ρ ⊤) : ‖evalHom δ ρ y T‖ = ‖y‖ * ‖evalHom δ ρ u T‖ := by
  change ‖T.1 y‖ = ‖y‖ * ‖T.1 u‖
  rw [norm_apply_eq hδ hρ T.2 y, norm_apply_eq hδ hρ T.2 u, hu, mul_one, mul_comm]

theorem evalHom_injective (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) :
    Function.Injective (evalHom δ ρ u) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h := norm_evalHom hδ hρ hu x T
  rw [hT, norm_zero, mul_zero] at h
  exact norm_eq_zero.1 h

theorem exists_op_unit (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y : X) {u : X} (hu : ‖u‖ = 1) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪u, x⟫_ℂ • T y := by
  have hinj := evalHom_injective hδ hρ hu
  let S : Submodule ℂ H := LinearMap.range (evalHom δ ρ u)
  let e := LinearEquiv.ofInjective (evalHom δ ρ u) hinj
  let L : S →ₗ[ℂ] H := evalHom δ ρ y ∘ₗ e.symm.toLinearMap
  have hL : ∀ v : S, ‖L v‖ ≤ ‖y‖ * ‖v‖ := fun v => by
    have h := norm_evalHom hδ hρ hu y (e.symm v)
    have h2 : evalHom δ ρ u (e.symm v) = v := congrArg Subtype.val (e.apply_symm_apply v)
    rw [h2] at h
    exact h.le
  have hLe : ∀ T : homIn δ ρ ⊤, L ⟨T.1 u, T, rfl⟩ = T.1 y := fun T => by
    have h : e.symm ⟨T.1 u, T, rfl⟩ = T := e.symm_apply_apply T
    change evalHom δ ρ y (e.symm ⟨T.1 u, T, rfl⟩) = T.1 y
    rw [h]
    rfl
  let K : Submodule ℂ H := S.topologicalClosure
  haveI : IsClosed (K : Set H) := S.isClosed_topologicalClosure
  haveI : CompleteSpace K := IsClosed.completeSpace_coe (s := (K : Set H))
  let i : S →ₗᵢ[ℂ] K := ⟨Submodule.inclusion S.le_topologicalClosure, fun _ => rfl⟩
  have hd : DenseRange i.toContinuousLinearMap := by
    refine Topology.IsInducing.subtypeVal.dense_iff.2 fun w => closure_mono (fun z hz => ?_) w.2
    exact ⟨⟨z, S.le_topologicalClosure hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  let B : K →L[ℂ] H := (L.mkContinuous ‖y‖ hL).extend i.toContinuousLinearMap
  have hB : ∀ v : S, B (i v) = L v := fun v =>
    ((L.mkContinuous ‖y‖ hL).extend_eq hd i.isometry.isUniformInducing v)
  refine ⟨B ∘L K.orthogonalProjection, fun T hT x => ?_⟩
  have hmem : ⟪u, x⟫_ℂ • T u ∈ K := K.smul_mem _ (S.le_topologicalClosure ⟨⟨T, hT⟩, rfl⟩)
  have horth : T x - ⟪u, x⟫_ℂ • T u ∈ Kᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro _ ⟨T', rfl⟩
    change ⟪T'.1 u, T x - ⟪u, x⟫_ℂ • T u⟫_ℂ = 0
    rw [inner_sub_right, inner_smul_right, inner_eq_be hδ hρ hT T'.2, inner_eq_be hδ hρ hT T'.2,
      inner_self_eq_norm_sq_to_K, hu]
    simp [mul_comm]
  have hproj : K.orthogonalProjection (T x) = ⟪u, x⟫_ℂ • i ⟨T u, ⟨T, hT⟩, rfl⟩ :=
    Subtype.ext (Submodule.eq_starProjection_of_mem_orthogonal hmem horth)
  change B (K.orthogonalProjection (T x)) = _
  rw [hproj, map_smul, hB, hLe ⟨T, hT⟩]

theorem exists_op (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y ξ : X) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪ξ, x⟫_ℂ • T y := by
  by_cases h0 : ξ = 0
  · exact ⟨0, fun T _ x => by simp [h0]⟩
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn' : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨A, hA⟩ := exists_op_unit hδ hρ y (u := (‖ξ‖ : ℂ)⁻¹ • ξ) (by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn])
  refine ⟨(‖ξ‖ : ℂ) • A, fun T hT x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hA T hT, inner_smul_left, smul_smul, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

theorem stOp : StOp := by
  intro G X H _ _ _ _ _ _ _ δ ρ hδ hρ _
  choose A hA using fun y ξ : X => exists_op (H := H) hδ hρ y ξ
  exact ⟨A, hA⟩

end GlobalTheory.CompanionTheory.RgFl
end
end

section

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

variable {G G' : Type} [Group G] [Group G']

def cosetEquiv (e : G ≃* G') (K : Subgroup G) : G ⧸ K ≃ G' ⧸ K.map e.toMonoidHom :=
  Quotient.congr (ra := QuotientGroup.leftRel K) (rb := QuotientGroup.leftRel (K.map e.toMonoidHom))
    e.toEquiv (by
      intro a b
      have h : (e.toEquiv a)⁻¹ * e.toEquiv b = e.toMonoidHom (a⁻¹ * b) := by simp
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, h]
      exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm)

lemma cosetEquiv_smul (e : G ≃* G') (K : Subgroup G) (g : G) (x : G ⧸ K) :
    cosetEquiv e K (g • x) = e g • cosetEquiv e K x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    change ((e (g * a) : G') : G' ⧸ K.map e.toMonoidHom) = ((e g * e a : G') : G' ⧸ K.map e.toMonoidHom)
    rw [map_mul]

theorem stSepMove : StSepMove := by
  intro G G' _ _ e K hK S
  classical
  let φ := cosetEquiv e K
  obtain ⟨Γ', hfin, hstab, hsep⟩ := hK (S.image φ)
  let Γ : Subgroup G := Γ'.comap e.toMonoidHom
  have hmem : ∀ γ : Γ, e (γ : G) ∈ Γ' := fun γ => γ.2
  have hsymm : ∀ γ' : Γ', e.symm (γ' : G') ∈ Γ := fun γ' => by
    change e (e.symm (γ' : G')) ∈ Γ'
    simpa using γ'.2
  have hact : ∀ (γ : Γ) (x : G ⧸ K), φ (γ • x) = (⟨e (γ : G), hmem γ⟩ : Γ') • φ x := fun γ x =>
    cosetEquiv_smul e K (γ : G) x
  refine ⟨Γ, ?_, ?_, ?_⟩
  · let f : MulAction.orbitRel.Quotient Γ' (G' ⧸ K.map e.toMonoidHom) →
        MulAction.orbitRel.Quotient Γ (G ⧸ K) :=
      Quotient.map' φ.symm (by
        rintro a b ⟨γ', rfl⟩
        refine ⟨⟨e.symm (γ' : G'), hsymm γ'⟩, ?_⟩
        apply φ.injective
        change φ (_ • φ.symm b) = φ (φ.symm (γ' • b))
        rw [hact]
        have h : (⟨e (e.symm (γ' : G')), hmem ⟨e.symm (γ' : G'), hsymm γ'⟩⟩ : Γ') = γ' :=
          Subtype.ext (e.apply_symm_apply _)
        rw [h, φ.apply_symm_apply, φ.apply_symm_apply])
    refine Finite.of_surjective f ?_
    intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      exact ⟨Quotient.mk'' (φ x),
        congrArg (Quotient.mk'' (s₁ := MulAction.orbitRel Γ (G ⧸ K))) (φ.symm_apply_apply x)⟩
  · intro x
    let f : MulAction.stabilizer Γ x → MulAction.stabilizer Γ' (φ x) := fun γ =>
      ⟨⟨e ((γ : Γ) : G), hmem γ⟩, by
        rw [MulAction.mem_stabilizer_iff, ← hact, MulAction.mem_stabilizer_iff.mp γ.2]⟩
    refine Finite.of_injective f ?_
    intro a b hab
    have h := congrArg (fun c : MulAction.stabilizer Γ' (φ x) => ((c : Γ') : G')) hab
    exact Subtype.ext (Subtype.ext (e.injective h))
  · intro x hx y hy γ hxy
    apply φ.injective
    exact hsep (φ x) (Finset.mem_image_of_mem φ hx) (φ y) (Finset.mem_image_of_mem φ hy)
      ⟨e (γ : G), hmem γ⟩ (by rw [← hact, hxy])

end GlobalTheory.CompanionTheory.RgFl
end

section

noncomputable section

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult

namespace GlobalTheory.CompanionTheory.FactorIso

theorem stIso : StIso := by
  intro G G₁ H _ _ _ _ _ _ π hπ j p hj hpj hc W hW
  haveI := hπ.complete
  have hu : IsUnitaryRep (π.comp j) := isUnitaryRep_comp hπ.unitary hj
  refine ⟨⟨W, hW.1.rep, isIrrUnitary_rep hu hW⟩, ?_⟩
  show isoPart hW.1.rep (π.comp j) ⊤ = ⊤
  have hsub : IsSubrep (π.comp j) (isoPart hW.1.rep (π.comp j) ⊤) := isSubrep_isoPart
  have hker : ∀ k, p k = 1 → ∀ v ∈ isoPart hW.1.rep (π.comp j) ⊤,
      π k v ∈ isoPart hW.1.rep (π.comp j) ⊤ := by
    intro k hk v hv
    have hle : isoPart hW.1.rep (π.comp j) ⊤ ≤
        (isoPart hW.1.rep (π.comp j) ⊤).comap (π k : H →ₗ[ℂ] H) :=
      isoPart_le (hsub.1.preimage (π k).continuous) fun T hT x =>
        apply_mem_isoPart (T := (π k).comp T) (mem_homIn_top.2 fun g y => by
          have hcomm : π k * π (j g) = π (j g) * π k := by
            rw [← map_mul, ← map_mul, (hc g k hk).eq]
          have hT' := hT.2 g y
          simp only [ContinuousLinearMap.comp_apply, hT', MonoidHom.comp_apply]
          exact DFunLike.congr_fun hcomm (T y)) x
    exact hle hv
  have hinv : IsSubrep π (isoPart hW.1.rep (π.comp j) ⊤) := by
    refine ⟨hsub.1, fun g v hv => ?_⟩
    have hg : g = j (p g) * ((j (p g))⁻¹ * g) := by group
    have h1 := hsub.2 (p g) _ (hker ((j (p g))⁻¹ * g) (by simp [hpj]) v hv)
    rw [hg, map_mul]
    simpa using h1
  rcases hπ.irred.2 _ hinv with h | h
  · exfalso
    apply hW.2.1
    rw [eq_bot_iff]
    intro w hw
    have hm : W.subtypeL ∈ homIn hW.1.rep (π.comp j) ⊤ := mem_homIn_top.2 fun _ _ => rfl
    have := apply_mem_isoPart hm ⟨w, hw⟩
    rw [h] at this
    simpa using this
  · exact h

end GlobalTheory.CompanionTheory.FactorIso

end
end

section

noncomputable section

open CompanionTheory.D.gk.admitted (stdPoly)
open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgFl

theorem proj_comm_of_star_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {N : Set (H →L[ℂ] H)} (hN : ∀ T ∈ N, star T ∈ N) (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (hS : ∀ T ∈ N, ∀ v ∈ S, T v ∈ S) (T : H →L[ℂ] H) (hT : T ∈ N) :
    T * S.starProjection = S.starProjection * T := by
  ext v
  have hperp : ∀ u, u ∈ Sᗮ → T u ∈ Sᗮ := by
    intro u hu
    rw [Submodule.mem_orthogonal] at hu ⊢
    intro w hw
    have h1 : ⟪w, T u⟫_ℂ = ⟪star T w, u⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hu _ (hS _ (hN T hT) _ hw)
  show T (S.starProjection v) = S.starProjection (T v)
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal (hS T hT _ (S.starProjection_apply_mem v))
  rw [← map_sub]
  exact hperp _ (S.sub_starProjection_mem_orthogonal v)

theorem stFactor_from (h1 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (E : H →L[ℂ] H) (m : ℕ), (∀ g : Fin m → G, stdPoly E (fun i => σ (g i)) = 0) →
    ∀ a : Fin m → (H →L[ℂ] H), (∀ i, ∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → T * a i = a i * T) → stdPoly E a = 0) (h2 : ∀ (G G₁ H : Type) [Group G] [Group G₁] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)), IsTopIrreducible π → ∀ (j : G₁ →* G) (p : G →* G₁),
    (∀ x, p (j x) = x) → (∀ x g, p g = 1 → Commute (j x) g) → ∀ x y : H →L[ℂ] H,
    (∀ T : H →L[ℂ] H, (∀ g, T * π (j g) = π (j g) * T) → T * y = y * T) → y ≠ 0 →
    (∀ g, x * π (j g) * y = 0) → x = 0) (h3 : ∀ (R : Type) [Ring R] (A S : Set R) (E : R) (m : ℕ) (q : Fin (m + 1) → R),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → S ⊆ A →
    (∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ S, x * s * y = 0) → x = 0) →
    (∀ a : Fin m → R, (∀ i, a i ∈ A) → stdPoly E a = 0) →
    (∀ i, q i ∈ A) → (∀ i, q i ≠ 0) → (∀ i, q i * q i = q i) → (∀ i k, i ≠ k → q i * q k = 0) →
    (∀ i, E * q i = q i) → False) (h4 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (L : Set (Submodule ℂ H)) (m : ℕ)
    (S₀ : Submodule ℂ H), (∀ S ∈ L, IsClosed (S : Set H)) → (∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L) → S₀ ∈ L → S₀ ≠ ⊥ →
    (∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) → ¬ Pairwise fun i k => f i ⟂ f k) →
    ∃ Q ∈ L, Q ≠ ⊥ ∧ ∀ T ∈ L, T ≤ Q → T = ⊥ ∨ T = Q) (h5 : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : Set (H →L[ℂ] H))
    (Q : Submodule ℂ H), (∀ T ∈ N, star T ∈ N) → IsClosed (Q : Set H) → (∀ T ∈ N, ∀ v ∈ Q, T v ∈ Q) →
    (∀ U : Submodule ℂ H, IsClosed (U : Set H) → U ≤ Q → (∀ T ∈ N, ∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = Q) →
    ∀ A : H →L[ℂ] H, (∀ T ∈ N, T * A = A * T) → ∃ c : ℂ, ∀ v ∈ Q, A v - c • v ∈ Qᗮ) (h6 : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W) : StFactor := by
  intro G G₁ H _ _ _ _ _ π hπ hirr j p hpj hcomm E hE
  obtain ⟨hE0, hEE, hEadj, hEc, m, hm⟩ := hE
  set ρ : G₁ →* (H →L[ℂ] H) := π.comp j with hρdef
  have hρ : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => hπ _ v
  let N : Set (H →L[ℂ] H) := {T | ∀ g, T * ρ g = ρ g * T}
  let A : Set (H →L[ℂ] H) := {T | ∀ n ∈ N, n * T = T * n}
  have hN : ∀ T ∈ N, star T ∈ N := by
    intro T hT g
    have h := congrArg star (hT g⁻¹)
    simp only [star_mul, CompanionTheory.D.gk.admitted.FinOfPIAux.star_eq ρ hρ, inv_inv] at h
    exact h.symm
  have hAmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A := by
    intro a ha b hb n hn
    rw [← mul_assoc, ha n hn, mul_assoc, hb n hn, mul_assoc]
  have hSA : Set.range ρ ⊆ A := by
    rintro _ ⟨g, rfl⟩ n hn
    exact hn g
  have hprime : ∀ x ∈ A, ∀ y ∈ A, y ≠ 0 → (∀ s ∈ Set.range ρ, x * s * y = 0) → x = 0 := by
    intro x _ y hy hy0 h
    exact h2 G G₁ H π hirr j p hpj hcomm x y (fun T hT => hy T hT) hy0 (fun g => h _ ⟨g, rfl⟩)
  have hPI : ∀ a : Fin m → (H →L[ℂ] H), (∀ i, a i ∈ A) → stdPoly E a = 0 :=
    fun a ha => h1 G₁ H ρ hρ E m hm a fun i T hT => ha i T hT
  let R : Submodule ℂ H := LinearMap.range (E : H →ₗ[ℂ] H)
  have hRmem : ∀ v, v ∈ R ↔ E v = v := by
    intro v
    constructor
    · rintro ⟨w, rfl⟩
      exact DFunLike.congr_fun hEE w
    · intro h
      exact ⟨v, h⟩
  have hRcl : IsClosed (R : Set H) := by
    have : (R : Set H) = {v | E v = v} := Set.ext hRmem
    rw [this]
    exact isClosed_eq E.continuous continuous_id
  let L : Set (Submodule ℂ H) :=
    {S | IsClosed (S : Set H) ∧ (∀ T ∈ N, ∀ v ∈ S, T v ∈ S) ∧ S ≤ R}
  have hRL : R ∈ L := by
    refine ⟨hRcl, fun T hT v hv => ?_, le_rfl⟩
    rw [hRmem] at hv ⊢
    have := DFunLike.congr_fun (hEc T hT) v
    simp only [mul_apply_eq_comp] at this
    rw [← this, hv]
  have hR0 : R ≠ ⊥ := by
    intro h
    apply hE0
    ext v
    have : E v ∈ R := ⟨v, rfl⟩
    rw [h] at this
    simpa using this
  have hLinf : ∀ S ∈ L, ∀ T ∈ L, S ⊓ Tᗮ ∈ L := by
    rintro S ⟨hS1, hS2, hS3⟩ U ⟨hU1, hU2, hU3⟩
    refine ⟨hS1.inter U.isClosed_orthogonal, fun T hT v hv => ⟨hS2 T hT v hv.1, ?_⟩, inf_le_left.trans hS3⟩
    have hv2 : v ∈ Uᗮ := hv.2
    show T v ∈ Uᗮ
    rw [Submodule.mem_orthogonal] at hv2 ⊢
    intro w hw
    have h1 : ⟪w, T v⟫_ℂ = ⟪star T w, v⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [h1]
    exact hv2 _ (hU2 _ (hN T hT) _ hw)
  have hbound : ∀ f : Fin (m + 1) → Submodule ℂ H, (∀ i, f i ∈ L) → (∀ i, f i ≠ ⊥) →
      ¬ Pairwise fun i k => f i ⟂ f k := by
    intro f hf hf0 hp
    have hc : ∀ i, CompleteSpace (f i) := fun i => (hf i).1.completeSpace_coe
    refine h3 (H →L[ℂ] H) A (Set.range ρ) E m (fun i => (f i).starProjection) hAmul hSA hprime hPI
      (fun i n hn => proj_comm_of_star_closed hN (f i) (hf i).2.1 n hn) (fun i h0 => hf0 i ?_) (fun i => ?_) (fun i k hik => ?_)
      (fun i => ?_)
    · rw [Submodule.eq_bot_iff]
      intro v hv
      have := Submodule.starProjection_eq_self_iff.mpr hv
      rw [← this, h0]
      rfl
    · ext v
      exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ v) |> fun h => h
    · ext v
      have hv : (f k).starProjection v ∈ (f i)ᗮ :=
        (hp hik).symm ((f k).starProjection_apply_mem v)
      exact Submodule.eq_starProjection_of_mem_orthogonal (zero_mem _) (by simpa using hv)
    · ext v
      exact (hRmem _).mp ((hf i).2.2 ((f i).starProjection_apply_mem v))
  obtain ⟨Q, hQL, hQ0, hQmin⟩ := h4 H L m R (fun S hS => hS.1) hLinf hRL hR0 hbound
  obtain ⟨ξ, hξ, hξ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
  refine h6 G₁ H ρ hρ Q ξ hQL.1 hξ hξ0 (fun T hT v hv => hQL.2.1 T hT v hv) (fun g => ?_)
  obtain ⟨c, hc⟩ := h5 H N Q hN hQL.1 hQL.2.1
    (fun U hU1 hU2 hU3 => hQmin U ⟨hU1, hU3, hU2.trans hQL.2.2⟩ hU2) (ρ g) (fun T hT => hT g)
  exact ⟨c, hc ξ hξ⟩

theorem stFactor : StFactor :=
  stFactor_from GlobalTheory.CompanionTheory.Factor.stdPoly_bicomm GlobalTheory.CompanionTheory.DirectFactor.bicommutant_restriction_prime GlobalTheory.CompanionTheory.PrimeRing.StdChain.no_orthogonal_idempotents GlobalTheory.CompanionTheory.OrthoFamily.exists_minimal_of_orthogonal_bound GlobalTheory.CompanionTheory.Factor.schur_on_minimal_subspace GlobalTheory.CompanionTheory.CyclicScalar.exists_isIrredSubrep

end GlobalTheory.CompanionTheory.RgFl

end
end
