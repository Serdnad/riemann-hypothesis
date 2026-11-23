module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle003

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolDescent

theorem exists_gen_of_unique {Y : Scheme.{0}} [Subsingleton Y] (y₀ : Y) {M : LB Y} (hM : M.IsLB) :
    ∃ t : LB.Gen M, t.IsGen := by
  obtain ⟨i₀, hi₀⟩ := exists_chart hM y₀
  have h : ∀ y, y ∈ M.U i₀ := fun y => by rwa [Subsingleton.elim y y₀]
  have le : ∀ i, M.U i ≤ M.U i ⊓ M.U i₀ := fun i => le_inf le_rfl fun y _ => h y
  refine ⟨⟨fun i => res (le i) (M.g i i₀)⟩, fun i j => unit_ext fun y hy => ?_⟩
  refine ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.1 _)).trans (Eq.symm ((map_mul _ _ _).trans ?_))
  refine (congrArg _ ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _))).trans ?_
  exact gm_cocycle hM _ y hy.1 hy.2 (h y)

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem kTriv_of_pullback [Flat f] [Surjective f] [IsAffineHom f] (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : Out.KTriv A' L') : Out.KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let R' : Type := Γ(pullback t f, ⊤)
  let e : Spec (CommRingCat.of R') ⟶ pullback t f := (pullback t f).isoSpec.inv
  have : IsIso e := inferInstanceAs (IsIso (pullback t f).isoSpec.inv)
  have : Epi (pullback.fst t f) := Flat.epi_of_flat_of_surjective _
  obtain ⟨q, t', hq, sq⟩ : ∃ (q : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
      (t' : Spec (CommRingCat.of R') ⟶ S'), Epi q ∧ q ≫ t = t' ≫ f :=
    ⟨e ≫ pullback.fst t f, e ≫ pullback.snd t f, inferInstance, by
      rw [Category.assoc, Category.assoc, pullback.condition]⟩
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have sx : (q ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ sx) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = q ≫ x.left := h.1.lift_fst _ _ _
  have main : x' = toUnit _ ≫ η[A'] := by
    refine hK R' t' x' fun p => ?_
    obtain ⟨V, hV, c, hc⟩ := hx (q p)
    refine ⟨q ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ q)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ q :=
      congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (snd T' A').left ≫ φ = (lift a b).left ≫ (snd T A).left :=
      (congrArg (fun q => q.left) (lift_snd a b)).symm
    have k₃ : ((fst T' A' ≫ x') * snd T' A').left ≫ φ = (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left := by
      have e₀ : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      have e₁ := h.2 (T' ⊗ A') (fst T' A' ≫ x') (snd T' A') (a ≫ x) b
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)) rfl
      rw [← e₀] at e₁
      exact e₁.symm
    obtain ⟨n, hn⟩ : ∃ n : ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ ((fst T A).left ⁻¹ᵁ V).toScheme,
        n ≫ ((fst T A).left ⁻¹ᵁ V).ι = ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left :=
      ⟨IsOpenImmersion.lift _ (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫ (lift a b).left) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact (congrArg (fun q => q y.1 ∈ V) k₁).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    let ψ : Fin 2 → (((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme ⟶ A'.left) := fun k =>
      ((fst T' A').left ⁻¹ᵁ (q ⁻¹ᵁ V)).ι ≫
        ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k => ψ k ≫ φ) _ _ n fun k => by
      rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
      fin_cases k
      exacts [congrArg (_ ≫ ·) k₃, congrArg (_ ≫ ·) k₂]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ ψ fun _ => rfl) c₃ h₃
  let a : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk q sq
  have e₁ : pushPt h.1.w x' = 1 := (congrArg _ main).trans (map_one (pushHom h T'))
  have e₂ : a ≫ x = a ≫ (1 : T ⟶ A) :=
    (Over.OverMorphism.ext hx'.symm : a ≫ x = pushPt h.1.w x').trans (e₁.trans (MonObj.comp_one a).symm)
  exact Over.OverMorphism.ext ((cancel_epi q).1 (congrArg (fun z => z.left) e₂))

theorem sym_of_pullback [Subsingleton S'] (s' : S') (h : IsGrpPullback A' A f φ) (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ))
    (desc : ∀ M : LB A.left, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (hS : Out.Sym A' L') : Out.Sym A L := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨U, hU, c, hc⟩ := hS s'
  obtain ⟨e, he⟩ : ∃ e : A'.left ⟶ (A'.hom ⁻¹ᵁ U).toScheme, e ≫ (A'.hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show A'.hom y ∈ U
      rwa [Subsingleton.elim (A'.hom y) s']), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullSame L' ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _] _ _ e fun k => by
    fin_cases k
    · exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans (Category.id_comp _))).symm
    · exact he.symm) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL hL' c₁ h₁
  obtain ⟨c₃, h₃⟩ := desc _ (DVR.linComb_isLB L hL ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1])
    (gen_chartPull (chartPullOut L _ _ φ _ fun k => by
      fin_cases k
      · exact inv_left_comp h
      · exact (Category.id_comp φ).trans (Category.comp_id φ).symm) c₂ h₂)
  intro s
  refine ⟨⊤, trivial, gen_chartPull (chartPullSame L _ _ _ (A.hom ⁻¹ᵁ ⊤).ι fun k => ?_) c₃ h₃⟩
  fin_cases k
  · rfl
  · exact (Category.comp_id _).symm

theorem rigidified_sym_kTriv_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left) (L₀ : LB A₀.left) (L : LB A.left), IsAbelianScheme A₀ → IsGrpPullback A A₀ (spMap i) φ → L₀.IsLB → L.IsLB → LBIso L (L₀.pull φ) → (Out.Rigidified A L → Out.Rigidified A₀ L₀) ∧ (Out.Sym A L → Out.Sym A₀ L₀) ∧ (Out.KTriv A L → Out.KTriv A₀ L₀) := by
  intro K₀ K _ _ i A₀ A _ _ φ L₀ L hA h hL₀ hL hw
  refine ⟨fun _ => ?_, fun hS => ?_, fun hK => ?_⟩
  · have : Subsingleton (𝟙_ (Over (Sp K₀))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
    exact exists_gen_of_unique (default : PrimeSpectrum K₀) (pull_isLB hL₀ _)
  · have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    exact sym_of_pullback (default : PrimeSpectrum K) h hL₀ hL hw
      (GlobalTheory.T.lineBundle_trivial_iso_descend_field K₀ K i _ _ A₀.hom A.hom φ hA.smooth hA.proper hA.geomConnected h.1).1 hS
  · have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    exact kTriv_of_pullback h hL₀ hL hw hK

end GlobalTheory.PolDescent
end
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IsoDescent

variable {X X' Y Y' : Scheme.{0}}

theorem exists_gen_of_invariant (M : LB Y) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (a : ∀ j, Γ(Y', m ⁻¹ᵁ M.U j)ˣ)
    (hc : ∀ (y : Y') i j, m y ∈ M.U i → m y ∈ M.U j →
      gm (𝟙 Y') y _ (a i) = gm m y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y') y _ (a j))
    (hinv : ∀ i (y : Y') j, m y ∈ M.U j → m (t i y) ∈ M.U j → gm (t i) y _ (a j) = gm (𝟙 Y') y _ (a j)) :
    ∃ v : LB.Gen M, v.IsGen := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have hex : ∀ j, ∃ b : Γ(Y, M.U j)ˣ, pullU m _ b = a j := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ M.U j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    exact hinv i y j hy (e hy)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j, y ∈ m ⁻¹ᵁ M.U j → gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (a j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans (congrArg _ (hb j))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans ((hc y i j hy.1 hy.2).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    ((gm_res _ y _ hy _).trans (val j hy.2)))

variable {L : LB X} {L' : LB X'} {K K' : Type} [Fintype K] [Fintype K']

theorem lbIso_of_invariant (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L' (fun k => m ≫ φ' k) ε')) (hu' : u'.IsGen)
    (hinv : ∀ i y J J', Good L y J → Good L' y J' →
      val u' (t i) y J' * (val u (t i) y J)⁻¹ = val u' (𝟙 Y') y J' * (val u (𝟙 Y') y J)⁻¹) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') := by
  have l₁ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L' (fun k => m ≫ φ' k) p.1 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
  have l₂ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L (fun k => m ≫ φ k) p.2 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have v : ∀ (r : Y' ⟶ Y') (y : Y') (p : (K' → L'.ι) × (K → L.ι)),
      r y ∈ m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) →
      gm r y _ (res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) =
        gm r y (LB.wchart L' (fun k => m ≫ φ' k) p.1) (u'.s p.1) *
          (gm r y (LB.wchart L (fun k => m ≫ φ k) p.2) (u.s p.2))⁻¹ := fun r y p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y _ h _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r y _ h _))))
  refine exists_gen_of_invariant (LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)) m t ht hd
    (fun p => res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) (fun y p q hp hq => ?_) (fun i y p hp hp' => ?_)
  · refine (v (𝟙 Y') y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div _ _ m y p q ⟨hp, hq⟩).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L' φ' ε' m y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε m y p.2 q.2 hp.2 hq.2))) (v (𝟙 Y') y q hq)).symm)
    rw [gen_trans hu' (𝟙 Y') y (l₁ p hp) (l₁ q hq), gen_trans hu (𝟙 Y') y (l₂ p hp) (l₂ q hq), mul_inv,
      mul_mul_mul_comm]
    simp only [trF, Category.id_comp]
  · choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    choose J' hJ' using fun χ : Y' ⟶ X' => exists_chart hL' (χ y)
    have gJ : Good L y J := hJ
    have gJ' : Good L' y J' := hJ'
    refine (v (t i) y p hp').trans (Eq.trans ?_ (v (𝟙 Y') y p hp).symm)
    rw [gen_trans hu' (t i) y (l₁ p hp') (gJ'.mem _ _), gen_trans hu (t i) y (l₂ p hp') (gJ.mem _ _),
      gen_trans hu' (𝟙 Y') y (l₁ p hp) (gJ'.mem _ _), gen_trans hu (𝟙 Y') y (l₂ p hp) (gJ.mem _ _),
      mul_inv, mul_inv, mul_mul_mul_comm, mul_mul_mul_comm (trF _ _ (𝟙 Y') _ _ _)]
    refine congrArg₂ (· * ·) ?_ (hinv i y J J' gJ gJ')
    have e : ∀ {W : Scheme.{0}} (χ : Y ⟶ W), t i ≫ m ≫ χ = 𝟙 Y' ≫ m ≫ χ := fun χ => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact congrArg₂ (fun a b => a * b⁻¹) (Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X' => gm ψ y (L'.U (p.1 k) ⊓ L'.U (J' ψ)) (L'.g (p.1 k) (J' ψ)) ^ ε' k) (e (φ' k)))
      (Finset.prod_congr rfl fun k _ => congrArg
        (fun ψ : Y' ⟶ X => gm ψ y (L.U (p.2 k) ⊓ L.U (J ψ)) (L.g (p.2 k) (J ψ)) ^ ε k) (e (φ k)))

theorem lbIso_of_gens (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (u' : LB.Gen (LB.LinComb L' φ' ε'))
    (hu' : u'.IsGen) : LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') :=
  lbIso_of_invariant hL hL' φ ε φ' ε' (𝟙 Y) (I := PEmpty) PEmpty.elim (fun i => i.elim)
    (fun _ f _ => ⟨f, rfl, fun _ h => h⟩) _ (DVR.pullGen_isGen _ _ _ u hu (𝟙 Y)) _
    (DVR.pullGen_isGen _ _ _ u' hu' (𝟙 Y)) (fun i => i.elim)

def chartPullDiv (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y
          (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartPullFlat (L : LB X) (F : X' ⟶ X) (e : ℤ) (ψ : K → (Y ⟶ X')) (ε : K → ℤ) (f : Y' ⟶ Y) :
    ChartPull ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f)
      (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e)) (𝟙 Y') :=
  have mem : ∀ (J : PUnit → K → PUnit → L.ι) (y : Y'),
      y ∈ ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J →
      ∀ k, ψ k (f y) ∈ LB.wchart L (fun _ : PUnit => F) (J PUnit.unit k) := fun J y hy k =>
    Set.mem_iInter.1 ((mem_pull (L := LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).1 hy) k
  have le : ∀ J : PUnit → K → PUnit → L.ι,
      ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J ≤
        LB.wchart L (fun k => f ≫ ψ k ≫ F) (fun k => J PUnit.unit k PUnit.unit) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem J y hy k) PUnit.unit
  { idx := fun J k => J PUnit.unit k PUnit.unit
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g _ f (𝟙 Y') y J J' hJ hJ').trans ((gm_linComb
        (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε (𝟙 Y' ≫ f) y (J PUnit.unit) (J' PUnit.unit)
        (Set.mem_iInter.2 (mem J y hJ)) (Set.mem_iInter.2 (mem J' y hJ'))).trans (Eq.trans
          (Finset.prod_congr rfl fun k _ => ?_) (gm_linComb L _ _ (𝟙 Y') y _ _ (le J hJ) (le J' hJ')).symm))
      refine (congrArg (· ^ ε k) (gm_linComb L (fun _ : PUnit => F) (fun _ => e) ((𝟙 Y' ≫ f) ≫ ψ k) y _ _
        (mem J y hJ k) (mem J' y hJ' k))).trans ?_
      rw [Fintype.prod_unique, ← zpow_mul, mul_comm e]
      simp only [Category.assoc] }

theorem exists_gen_div_pull {W : Scheme.{0}} (L : LB X) (L' : LB X') (F : W ⟶ X) (F' : W ⟶ X') (e e' : ℤ)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e))
      (LB.LinComb L' (fun k => f ≫ ψ k ≫ F') (fun k => ε k * e'))) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb (LB.LinComb L' (K := PUnit) (fun _ => F') (fun _ => e')) ψ ε)
      (LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullFlat L F e ψ ε f) (chartPullFlat L' F' e' ψ ε f)
  exact gen_chartPull (chartPullDiv _ _ f) w hw

end GlobalTheory.IsoDescent
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.WeilFieldExt

open GlobalTheory.CommPairing ReciprocityTheory.ChartRestriction.G.Out

theorem corr_of_val_epi {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (q : Y' ⟶ Y) [Epi q]
    (hq : ∀ U : Y.Opens, Function.Injective (q.app U).hom)
    (h : ∀ y J, Good L y J → val t q y J = val t' q y J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have inj : Function.Injective (pullU q (LB.wchart L φ j ⊓ LB.wchart L φ' j')) := fun a b e =>
    Units.ext (hq _ (congrArg Units.val e))
  apply inj
  refine unit_ext fun y hy => ?_
  have hy' : q y ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hy
  obtain ⟨J, hJ, e⟩ := exists_good L hL y (fun k => q ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    intro a b e
    have e := (cancel_epi q).1 e
    rcases a with a | a <;> rcases b with b | b
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hy'.1 a, Set.mem_iInter.1 hy'.2 a])
  have := h y J hJ
  rw [val_of t _ y J j (fun k => e (.inl k)), val_of t' _ y J j' (fun k => e (.inr k))] at this
  exact (gm_id_pull q y _ hy' _).trans ((gm_res _ y _ hy' _).trans (this.trans
    ((gm_res _ y _ hy' _).symm.trans (gm_id_pull q y _ hy' _).symm)))

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

omit [GrpObj A] in
theorem isPullback_whisker {T T' : Over S} (h : T' ⟶ T) :
    IsPullback (h ▷ A).left (fst T' A).left (fst T A).left h.left := by
  refine (IsPullback.of_right (h₁₁ := (h ▷ A).left) (v₁₁ := pullback.fst T'.hom A.hom)
    (h₁₂ := pullback.snd T.hom A.hom) (v₁₂ := pullback.fst T.hom A.hom) (h₂₁ := h.left) (h₂₂ := T.hom)
    (v₁₃ := A.hom) ?_ ?_ (IsPullback.of_hasPullback T.hom A.hom).flip)
  · have e : (h ▷ A).left ≫ pullback.snd T.hom A.hom = pullback.snd T'.hom A.hom :=
      congrArg (fun q => q.left) (whiskerRight_snd h A)
    rw [e, Over.w h]
    exact (IsPullback.of_hasPullback T'.hom A.hom).flip
  · exact congrArg (fun q => q.left) (whiskerRight_fst h A)

theorem commIsOf_descend (hA : IsAbelianScheme A) (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    [Epi (h ▷ A).left] (hq : ∀ U, Function.Injective ((h ▷ A).left.app U).hom)
    {θx θy : ThetaGrp A L k T} {a b : ThetaGrp A L k T'} (ha : a.pt = h ≫ θx.pt) (hb : b.pt = h ≫ θy.pt)
    {c : Γ(T.left, ⊤)ˣ} (H : CommIsOf A L k a b (Units.map h.left.appTop.hom.toMonoidHom c)) :
    CommIsOf A L k θx θy c := by
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1
    (commIsOf_change globalFns_holds hA hL (hx.trans ha.symm) (hy.trans hb.symm) H)
  refine corr_of_val_epi hL (h ▷ A).left hq fun z J hJ => ?_
  have key : ∀ θ θ' : ThetaGrp A L k T,
      val (LB.mulGen L _ _ _ _ θ.φ (LB.pullGen L _ _ θ'.φ (translT A θ.pt).left)) (h ▷ A).left z J =
        tval θ (h ▷ A).left z J * tval θ' ((h ▷ A).left ≫ (translT A θ.pt).left) z J := fun θ θ' =>
    (val_mul hJ _ _ _).trans (congrArg (tval θ (h ▷ A).left z J * ·) (val_pull hJ _ _ _))
  have e := H' _ (𝟙 _) z J hJ
  have t : ∀ x : T ⟶ A, (𝟙 _ ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (h ▷ A).left ≫ (translT A x).left := fun x => by
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (𝟙 _ ≫ (fst T' A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom c) =
      gm ((h ▷ A).left ≫ (fst T A).left) z ⊤ c := by
    refine (gm_pull (𝟙 _ ≫ (fst T' A).left) h.left z ⊤ trivial c).trans ?_
    rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t, g, Category.id_comp] at e
  exact (key θx θy).trans (e.trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (key θy θx) (H1.val_constGen L c _ z J))).symm)

theorem weilIs_iff (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S} [Unique T.left] (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k x y c ↔
      ∃ θx θy : ThetaGrp A L k T, θx.pt = x ∧ θy.pt = y ∧ CommIsOf A L k θx θy c := by
  constructor
  · intro H
    obtain ⟨V, hp, ⟨θx, θy, hx, hy⟩, hc⟩ := H default
    obtain rfl : V = ⊤ := eq_top_iff.2 fun p _ => by rwa [Unique.eq_default p]
    let s : T ⟶ overRes (⊤ : T.left.Opens) := Over.homMk T.left.topIso.inv (by
      show T.left.topIso.inv ≫ T.left.topIso.hom ≫ T.hom = T.hom
      rw [Iso.inv_hom_id_assoc])
    have w : s.left ≫ (⊤ : T.left.Opens).ι = 𝟙 _ := T.left.topIso.inv_hom_id
    have w' : s ≫ overResι ⊤ = 𝟙 T := Over.OverMorphism.ext w
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL s (hc θx θy hx hy)
    rw [hx, ← Category.assoc, w', Category.id_comp] at ha
    rw [hy, ← Category.assoc, w', Category.id_comp] at hb
    have e : Units.map s.left.appTop.hom.toMonoidHom (unitRes ⊤ c) = c := by
      apply Units.ext
      have := congrArg (fun q => q.appTop.hom c.val) w
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
      exact this
    rw [e] at H'
    exact ⟨a, b, ha, hb, H'⟩
  · rintro ⟨θx, θy, rfl, rfl, H⟩ p
    obtain ⟨a, b, ha, hb, H'⟩ := exists_commIsOf_pull hL (overResι (⊤ : T.left.Opens)) H
    exact ⟨⊤, trivial, ⟨a, b, ha, hb⟩, fun a' b' ha' hb' =>
      commIsOf_change globalFns_holds hA hL (ha'.trans ha.symm) (hb'.trans hb.symm) H'⟩

theorem exists_lift_descend (hL : L.IsLB) {T T' : Over S} (h : T' ⟶ T)
    (hd : ∀ M : LB (T ⊗ A).left, M.IsLB → (∃ t : (M.pull (h ▷ A).left).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen)
    (x : T ⟶ A) (a : ThetaGrp A L k T') (ha : a.pt = h ≫ x) : ∃ θ : ThetaGrp A L k T, θ.pt = x := by
  obtain ⟨t, ht⟩ := hd (thetaLB A L k x) (DVR.linComb_isLB L hL _ _)
    (gen_chartPull (chartPullOut L ![(snd T A).left, (translPt A x).left] ![k, -k] (h ▷ A).left
      ![(snd T' A).left, (translPt A a.pt).left] (fun i => by
        fin_cases i
        · exact (congrArg (fun q => q.left) (whiskerRight_snd h A)).symm
        · show (translPt A a.pt).left = (h ▷ A).left ≫ (translPt A x).left
          rw [← Over.comp_left, whisker_translPt, ha])) a.φ a.isGen)
  exact ⟨⟨x, t, ht⟩, rfl⟩

theorem unitOn_map {K Ω : Type} [CommRing K] [CommRing Ω] (i : K →+* Ω) (c : Kˣ) :
    unitOn (Units.map i.toMonoidHom c) = Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) := by
  apply Units.ext
  exact congrArg (fun q => q.hom c.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))

end GlobalTheory.WeilFieldExt

namespace GlobalTheory


open WeilFieldExt CommPairing in
theorem weilIs_fieldExt_iff : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (K Ω : Type) [Field K] [Field Ω] (i : K →+* Ω) (x : Sp K ⟶ S) (L : LB G.left) (k : ℤ) (y y' : Over.mk x ⟶ G) (c : Kˣ), IsAbelianScheme G → L.IsLB → (Out.WeilIs G L k ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ((Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y') (unitOn (Units.map i.toMonoidHom c)) ↔ Out.WeilIs G L k y y' (unitOn c)) := by
  intro S G _ K Ω _ _ i x L k y y' c hG hL
  rw [unitOn_map]
  let h : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  refine ⟨fun H => ?_, fun H => weilIs_pull globalFns_holds hG hL h H⟩
  letI : Unique (Over.mk x).left := inferInstanceAs (Unique (PrimeSpectrum K))
  letI : Unique (Over.mk (spMap i ≫ x)).left := inferInstanceAs (Unique (PrimeSpectrum Ω))
  obtain ⟨a, b, ha, hb, Hc⟩ := (weilIs_iff hG hL _ _ _).1 H
  have pb : IsPullback (h ▷ G).left (fst _ G).left (fst _ G).left (spMap i) := isPullback_whisker h
  obtain ⟨e, -, -, -, inj⟩ := (FieldBaseChange.epi_and_isMonHom_iff K Ω i).1 _ _ _ _ _ pb
  have hd := (GlobalTheory.T.lineBundle_trivial_iso_descend_field K Ω i _ _ _ _ _
    (by have := hG.smooth; exact inferInstanceAs (Smooth (pullback.fst x G.hom)))
    (by have := hG.proper; exact inferInstanceAs (IsProper (pullback.fst x G.hom)))
    (by have := hG.geomConnected; exact inferInstanceAs (GeometricallyConnected (pullback.fst x G.hom))) pb).1
  obtain ⟨θ, rfl⟩ := exists_lift_descend hL h hd y a ha
  obtain ⟨θ', rfl⟩ := exists_lift_descend hL h hd y' b hb
  exact (weilIs_iff hG hL _ _ _).2 ⟨θ, θ', rfl, rfl, commIsOf_descend hG hL h inj ha hb Hc⟩

end GlobalTheory
end
end
