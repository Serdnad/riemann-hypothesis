module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle118
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.ShortSum

variable {X : Type} [AddCommGroup X]

abbrev mulSub (X : Type) [AddCommGroup X] (k : ℕ) : AddSubgroup X := (nsmulAddMonoidHom (α := X) k).range

theorem mk_eq_iff (k : ℕ) (a b : X) :
    (QuotientAddGroup.mk a : X ⧸ mulSub X k) = QuotientAddGroup.mk b ↔ ∃ z, b = a + k • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : k • z = -a + b := hz
    rw [this]; abel
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩

theorem surj {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Function.Surjective (fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨i, z, hz⟩ := h.2.2.1 a
  exact ⟨i, (mk_eq_iff k _ _).2 ⟨z, hz⟩⟩

theorem sum_comp {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu)
    [Fintype (X ⧸ mulSub X k)] (g : X ⧸ mulSub X k → ℤ) :
    ∑ i, g (QuotientAddGroup.mk (cls i)) = mu * ∑ c, g c := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨i₀, rfl⟩ := surj h c
  rw [Finset.sum_congr rfl (g := fun _ => g (QuotientAddGroup.mk (cls i₀)))
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← h.2.2.2 i₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => by simp only [hi]⟩
  exact h.2.1 i i₀ ((mk_eq_iff k _ _).1 hi.symm)

theorem val_eq {k r r' mu mu' : ℕ} {Q : X → ℤ} {cls : Fin r → X} {cls' : Fin r' → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') {i : Fin r} {i' : Fin r'}
    (e : (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k) = QuotientAddGroup.mk (cls' i')) :
    Q (cls i) = Q (cls' i') := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e
    rw [hz]; exact h.1 i z
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e.symm
    rw [hz]; exact h'.1 i' z

theorem sum_eq {k r mu mu' : ℕ} {Q : X → ℤ} {cls cls' : Fin r → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') : ∑ i, Q (cls i) = ∑ i, Q (cls' i) := by
  haveI : Finite (X ⧸ mulSub X k) := Finite.of_surjective _ (surj h)
  letI : Fintype (X ⧸ mulSub X k) := Fintype.ofFinite _
  have a := sum_comp h (fun _ => 1)
  have a' := sum_comp h' (fun _ => 1)
  have hm : (mu : ℤ) = mu' := by
    have hp : (∑ _c : X ⧸ mulSub X k, (1 : ℤ)) ≠ 0 := by simp
    exact mul_right_cancel₀ hp (a.symm.trans a')
  have b := sum_comp h (fun c => Q (cls (Function.surjInv (surj h) c)))
  have b' := sum_comp h' (fun c => Q (cls (Function.surjInv (surj h) c)))
  calc ∑ i, Q (cls i) = _ := Finset.sum_congr rfl fun i _ =>
        val_eq h h (Function.surjInv_eq (surj h) _).symm
    _ = _ := b
    _ = _ := by rw [hm]
    _ = _ := b'.symm
    _ = _ := Finset.sum_congr rfl fun i _ => val_eq h h' (Function.surjInv_eq (surj h) _)

theorem transport {X₀ : Type} [AddCommGroup X₀] {q₀ : X₀ → ℤ} {Q : X → ℤ} (e : X₀ ≃+ X) {w : ℕ} (hw : 0 < w)
    (hQ : ∀ y, Q (e y) = w * q₀ y) {k r mu : ℕ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Adapted k q₀ (fun i => e.symm (cls i)) mu := by
  refine ⟨fun i z => ?_, fun i i' ⟨z, hz⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩
  · have h1 := h.1 i (e z)
    have h2 := hQ (e.symm (cls i))
    have h3 := hQ (e.symm (cls i) + k • z)
    rw [map_add (f := _), map_nsmul] at h3
    rw [e.apply_symm_apply] at h2 h3
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hw)
  · have h1 := congrArg e hz
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply] at h1
    simp only [h.2.1 i i' ⟨_, h1⟩]
  · obtain ⟨i, z, hz⟩ := h.2.2.1 (e α)
    refine ⟨i, e.symm z, e.injective ?_⟩
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply]
    exact hz
  · rw [← h.2.2.2 i₀]
    simp only [e.symm.injective.eq_iff]

end GlobalTheory.OneBasis.ShortSum

namespace GlobalTheory.OneBasis

theorem sum_adapted_eq : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  intro X₀ _ _ _ q₀ k r hk hq
  by_cases hex : ∃ (c₀ : Fin r → X₀) (m₀ : ℕ), Adapted k q₀ c₀ m₀
  · obtain ⟨c₀, m₀, h₀⟩ := hex
    refine ⟨k, (∑ i, q₀ (c₀ i)).toNat, hk, fun X _ Q e w hw hQ cls mu h => ?_⟩
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hq _),
      ShortSum.sum_eq h₀ (ShortSum.transport e hw hQ h)]
    have : ∑ i, Q (cls i) = w * ∑ i, q₀ (e.symm (cls i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hQ, e.apply_symm_apply]
    rw [this]; ring
  · exact ⟨k, 0, hk, fun X _ Q e w hw hQ cls mu h => (hex ⟨_, _, ShortSum.transport e hw hQ h⟩).elim⟩

end GlobalTheory.OneBasis
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Compare

theorem eSec_comm_of_pullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem wVal_tri {X X' X'' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
    {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
    (T : Tri w w' w'') (y : Y) {J J' J''} (hJ : Good L y J) (hJ' : Good L' y J') (hJ'' : Good L'' y J'')
    (a : Y ⟶ X'') : GlobalTheory.ConstFam.wVal w'' y J J'' a =
      GlobalTheory.ConstFam.wVal w y J J' (a ≫ F') * GlobalTheory.ConstFam.wVal w' y J' J'' a := by
  have := T Y a y (J (a ≫ F' ≫ F)) (J' (a ≫ F')) (J'' a) (hJ (a ≫ F' ≫ F)) (hJ' (a ≫ F')) (hJ'' a)
  simpa only [GlobalTheory.ConstFam.wVal, Category.assoc] using this

theorem rigPull_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  intro Z G₀ _ L₀ hL₀ ρ₀ S S' x f G _ G' _ L L' hL hL' φ φ' w w' ρ ρ' ⟨gp, hw, hρ, hm⟩ ⟨gp', hw', hρ', hm'⟩
  obtain ⟨ψ, e₁, e₂⟩ : ∃ ψ : G'.left ⟶ G.left, ψ ≫ φ = φ' ∧ ψ ≫ G.hom = G'.hom ≫ f :=
    ⟨gp.1.lift φ' (G'.hom ≫ f) (by rw [gp'.1.w, Category.assoc]), gp.1.lift_fst _ _ _, gp.1.lift_snd _ _ _⟩
  subst e₁
  have gψ : IsGrpPullback G' G f ψ := gp.cancel gp' e₂
  have pw := (isGen_iff w).1 hw
  have pw' := (isGen_iff w').1 hw'
  obtain ⟨ω, T⟩ := exists_cancel hL₀ w w' pw pw' hL hL'
  refine ⟨ψ, ω, ⟨gψ, (isGen_iff ω).2 (T.pgen_cancel hL₀ pw pw'), hρ',
    T.pmaps_cancel hL₀ (fun _ => eSec_comm_of_pullback gψ) hm hm'⟩, ?_⟩
  intro k T₀ T₁ T' p q hp hq s₀ s s' H H' Y r' r h₁ h₂ z J J' hJ hJ'
  obtain ⟨J₀, hJ₀⟩ := GlobalTheory.ConstFam.exists_good' hL₀ z
  have hw₀ : (r ≫ (fst T₁ G).left ≫ p) ≫ T₀.hom = (r ≫ (snd T₁ G).left ≫ φ) ≫ G₀.hom := by
    simp only [Category.assoc]
    rw [hp, gp.1.w, ← Category.assoc (fst T₁ G).left, ← Category.assoc (snd T₁ G).left, Over.w, Over.w]
  obtain ⟨r₀, a₁, a₂⟩ : ∃ r₀ : Y ⟶ (T₀ ⊗ G₀).left, r₀ ≫ (fst T₀ G₀).left = r ≫ (fst T₁ G).left ≫ p ∧
      r₀ ≫ (snd T₀ G₀).left = r ≫ (snd T₁ G).left ≫ φ :=
    ⟨pullback.lift _ _ hw₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have b₁ := H Y r r₀ a₁ a₂ z J₀ J hJ₀ hJ
  have b₂ := H' Y r' r₀ (by rw [a₁, ← Category.assoc, h₁]; simp only [Category.assoc])
    (by rw [a₂, ← Category.assoc, h₂]; simp only [Category.assoc]) z J₀ J' hJ₀ hJ'
  rw [wVal_tri T z hJ₀ hJ hJ', Category.assoc, ← h₂, b₁, Units.val_mul, mul_pow, _root_.mul_assoc,
    ← Units.val_pow_eq_pow_val] at b₂
  exact (Units.mul_right_inj _).1 b₂

end GlobalTheory.OneBasis.Compare
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem GlobalTheory.OneBasis.exists_rigPull_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (K : Type) [Field K] (x : Sp K ⟶ Z), PolAt t x → ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ t.G.left) (w : LB.Iso A.L (t.PP.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A))), RigPull A.A t.G x φ w ρ t.PP.rig := by
  intro _ _ E _ _ _ H Z t K _ x ⟨hp, hA, hK⟩
  have hsemi : IsSemiAbelian ((Over.pullback x).obj t.G) := by
    refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
    · have := t.semi.comm
      infer_instance
    · have := t.semi.smooth
      change Smooth (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.separated
      change IsSeparated (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.quasiCompact
      change QuasiCompact (pullback.snd t.G.hom x)
      infer_instance
    · have := t.semi.geomConnected
      change GeometricallyConnected (pullback.snd t.G.hom x)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ x)
      exact ⟨torusExtOfIso (pullCompIso q x t.G) A⟩
  have hpull : ∃ (PP' : RigLB ((Over.pullback x).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
      (m : SABMap ⟨(Over.pullback x).obj t.G, hsemi,
        Geo.Tor.OAct.pullback x t.G t.act, PP', cub, sym, adj, prim⟩ t x),
      m.φ = pullback.fst t.G.hom x := by
    have h := isGrpPullback_pullback t.G x
    obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
    have hact : ∀ a, ((Geo.Tor.OAct.pullback x t.G t.act).act a).left ≫ pullback.fst t.G.hom x =
        pullback.fst t.G.hom x ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
    have pa : ∀ {T : Over _} (y : T ⟶ (Over.pullback x).obj t.G) a,
        pushPt h.1.w (y ≫ (Geo.Tor.OAct.pullback x t.G t.act).act a) = pushPt h.1.w y ≫ t.act.act a := fun y a =>
      Over.OverMorphism.ext (by
        show (y.left ≫ _) ≫ _ = (y.left ≫ _) ≫ _
        rw [Category.assoc, hact, Category.assoc])
    refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
    · let U := lift (pushPt h.1.w (fst ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
        (pushPt h.1.w (snd ((Over.pullback x).obj t.G) ((Over.pullback x).obj t.G)))
      refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
      · fin_cases i
        · exact (pa _ a).trans (by simp [U])
        · simp [U]
      · fin_cases i
        · simp [U]
        · exact (pa _ _).trans (by simp [U])
    · let U := pushPt h.1.w (𝟙 ((Over.pullback x).obj t.G))
      refine LBIso.chartPull (chartPullPull t.PP.L _)
        (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
      fin_cases i
      · simp [U]
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := hpull
  let t' : SAB H (Spec (CommRingCat.of K)) :=
    ⟨(Over.pullback x).obj t.G, hsemi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t x := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom x := hm₁
  obtain ⟨w, hw, hr, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x)) := hm₀ ▸ ⟨w, hw⟩
  have hM := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom x)
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom x)).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  have hP : PMaps w (K := PUnit) (fun _ => eSec t'.G) (fun _ => eSec t.G) (fun _ => 1) t'.PP.rig t.PP.rig m₀.cm.e :=
    (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig m₀.cm.e _
      (rigPull_le m₀.cm.F m₀.cm.e m₀.cm.e_comm t.PP.L) (fun _ => rfl)).1 hr
  rw [m₀.base] at hP
  exact ⟨GlobalTheory.GenericPol.toPolAV t' g hg hp hA' hK', m₀.cm.F, w, t'.PP.rig, m₀.cart, hw, t'.PP.rigGen, hP⟩
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Calc
open GlobalTheory.FrameGen GlobalTheory.ConstFam

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L' : LB G'.left}
  {L : LB G.left} {w : LB.Iso L' (L.pull φ)} {k : ℕ} {T' : Over S'} {T T₁ : Over S}

theorem prod_ext' {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_lift {Z : Scheme.{0}} (a : Z ⟶ T.left) (b : Z ⟶ G.left) (e : a ≫ T.hom = b ≫ G.hom) :
    ∃ H : Z ⟶ (T ⊗ G).left, H ≫ (fst T G).left = a ∧ H ≫ (snd T G).left = b :=
  ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_w : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := (Over.w _).trans (Over.w _).symm

theorem exists_prod (hφ : φ ≫ G.hom = G'.hom ≫ f) {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ G').left ⟶ (T ⊗ G).left, H ≫ (fst T G).left = (fst T' G').left ≫ h ∧
      H ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  exists_lift _ _ (by rw [Category.assoc, Category.assoc, hh, hφ, ← Category.assoc, ← Category.assoc, prod_w])

theorem thru_sv {h : T'.left ⟶ T.left} {s : LB.Sec (LPow G L (k : ℤ) T)} {s' : LB.Sec (LPow G' L' (k : ℤ) T')}
    (H : Thru w k h s s') {Z : Scheme.{0}} (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left)
    (h₁ : r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h) (h₂ : r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ)
    (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sv G L k s r z J = (wVal w z J J' (r' ≫ (snd T' G').left) ^ k).val * sv G' L' k s' r' z J' := by
  rw [Units.val_pow_eq_pow_val]
  exact H Z r' r h₁ h₂ z J J' hJ hJ'

theorem existsUnique_thru (hφ : φ ≫ G.hom = G'.hom ≫ f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) (s : LB.Sec (LPow G L (k : ℤ) T)) :
    ∃! t : LB.Sec (LPow G' L' (k : ℤ) T'), Thru w k h s t := by
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hh
  obtain ⟨t, ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' G').left)
    (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (h := H) hw hL hL' (fun _ => h₂.symm) s
  have key : Thru w k h s t := fun Z r' r e₁ e₂ z J J' hJ hJ' => by
    obtain rfl : r = r' ≫ H := prod_ext' (by rw [Category.assoc, h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
    have a := ht.sval (fun _ => h₂.symm) r' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at a
  refine ⟨t, key, fun t' ht' => SecOps.sec_ext (sec_ext_val hL' fun y J' hJ' => ?_)⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ : H ≫ (fst T G).left = 𝟙 _ ≫ (fst T' G').left ≫ h := by rw [Category.id_comp, h₁]
  have e₂ : H ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G').left ≫ φ := by rw [Category.id_comp, h₂]
  exact (Units.mul_right_inj _).1 ((thru_sv ht' _ H e₁ e₂ y hJ hJ').symm.trans (thru_sv key _ H e₁ e₂ y hJ hJ'))

theorem cmb_iff (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (k : ℤ) T)) (a : Fin n → Γ(T.left, ⊤))
    (t : LB.Sec (LPow G L (k : ℤ) T)) :
    ((∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J) ∧
    ((∀ (z : (T ⊗ G).left) (J), Good L z J →
      sv G L k t (𝟙 _) z J = ∑ i, gT (𝟙 _ ≫ (fst T G).left) z (a i) * sv G L k (b i) (𝟙 _) z J) →
      ∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) := by
  have key : ∀ t : LB.Sec (LPow G L (k : ℤ) T), (∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J := fun t H Z r z J hJ =>
    (SectionScalarValuation.sval_lin (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (s := t)
      (fun i => (fst T G).left.appTop.hom (a i)) b H r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ((gs_top _ _ _).trans (gT_comp _ _ _ _)) rfl)
  refine ⟨key t, fun H j => ?_⟩
  let σ := SectionLimit.linSec (fun i => (fst T G).left.appTop.hom (a i)) b
  exact sec_ext_val (s := t) (s' := σ) hL (fun y J hJ => (H y J hJ).trans (key σ (fun _ => rfl) _ _ y J hJ).symm) j

theorem cmb_of_lin (hφ : φ ≫ G.hom = G'.hom ≫ f) (hL : L.IsLB) (hL' : L'.IsLB) {g : T'.left ⟶ T₁.left}
    (hg : g ≫ T₁.hom = T'.hom ≫ f) {h : T₁ ⟶ T} {p : T'.left ⟶ T.left} (hp : p = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {c : Fin n → Γ(T₁.left, ⊤)} {s : LB.Sec (LPow G L (k : ℤ) T₁)}
    {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')} {t : LB.Sec (LPow G' L' (k : ℤ) T')} (hl : Lin G L k h b c s)
    (hb : ∀ i, Thru w k p (b i) (b' i)) (ht : Thru w k g s t) :
    ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  subst hp
  refine (cmb_iff hL' b' _ t).2 fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hg
  have e := lin_all hL hl H z hJ
  rw [thru_sv ht (𝟙 _) H (by rw [Category.id_comp, h₁]) (by rw [Category.id_comp, h₂]) z hJ hJ'] at e
  refine (Units.mul_right_inj _).1 (e.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [thru_sv (hb i) (𝟙 _) (H ≫ (h ▷ G).left)
    (by rw [Category.id_comp, Category.assoc, wh_fst, ← Category.assoc, h₁, Category.assoc])
    (by rw [Category.id_comp, Category.assoc, wh_snd, h₂]) z hJ hJ', gT_comp, h₁, Category.id_comp,
    Category.id_comp, mul_left_comm]

theorem exists_thru_up (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _) :
    ∃ H : (T₁ ⊗ G).left ⟶ (T' ⊗ G').left, H ≫ (fst T' G').left ≫ g = (fst T₁ G).left ∧
      H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left ∧
      ∀ t : LB.Sec (LPow G' L' (k : ℤ) T'), ∃ s : LB.Sec (LPow G L (k : ℤ) T₁), Thru w k g s t := by
  have hp : (snd T₁ G).left ≫ G.hom = (((fst T₁ G).left ≫ p) ≫ T'.hom) ≫ f := by
    rw [Category.assoc, ← hg, Category.assoc, ← Category.assoc p, pg, Category.id_comp, prod_w]
  obtain ⟨H, h₁, h₂⟩ := exists_lift (T := T') (G := G') ((fst T₁ G).left ≫ p) (hφ.lift _ _ hp) (hφ.lift_snd _ _ hp).symm
  have h₃ : H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left := by rw [← Category.assoc, h₂, hφ.lift_fst]
  refine ⟨H, by rw [← Category.assoc, h₁, Category.assoc, pg, Category.comp_id], h₃, fun t => ?_⟩
  obtain ⟨t₁, ht₁⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ))
    ((isGen_iff w).1 hw) hL hL' t
  obtain ⟨s, -, hs⟩ := SectionLimit.exists_pull t₁ H (fun _ : Fin 1 => (snd T₁ G).left) (fun _ => h₃)
  refine ⟨s, fun Z r' r e₁ e₂ z J J' hJ hJ' => ?_⟩
  have e₁' : r ≫ H ≫ (fst T' G').left = r' ≫ (fst T' G').left := by
    rw [h₁, ← Category.assoc, e₁, Category.assoc, Category.assoc, gp, Category.comp_id]
  have e : r ≫ H = r' := prod_ext' (by rw [Category.assoc, e₁']) (hφ.hom_ext
    (by rw [Category.assoc, Category.assoc, h₃, e₂, Category.assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, ← prod_w, ← Category.assoc H, ← Category.assoc, e₁',
      Category.assoc]))
  have ST : SecThrough w (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T' G').left ≫ φ) (fun _ => (k : ℤ)) t t₁
      (𝟙 _) := fun Z r z p q hp hq => by
    rw [Category.comp_id]
    exact ht₁ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  have a := ST.sval (fun _ => (Category.id_comp _).symm) r' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, Category.comp_id] at a
  exact (hs Z r z J hJ).trans ((congrArg (fun q => sval t₁ q z J) e).trans a)

theorem basis_thru (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _)
    {h : T₁ ⟶ T} {q : T'.left ⟶ T.left} (hq : q = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')}
    (hB : BasisAlong G L k h b) (hb : ∀ i, Thru w k q (b i) (b' i)) (t : LB.Sec (LPow G' L' (k : ℤ) T')) :
    ∃! c : Fin n → Γ(T₁.left, ⊤), ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  obtain ⟨H, h₁, h₃, hs⟩ := exists_thru_up (k := k) hφ hw hL hL' hg gp pg
  obtain ⟨s, hst⟩ := hs t
  obtain ⟨c, hc, hu⟩ := hB s
  refine ⟨c, cmb_of_lin hφ.w hL hL' hg hq hc hb hst, fun c' hc' => hu c' fun z J hJ => ?_⟩
  subst hq
  obtain ⟨J', hJ'⟩ := exists_good' hL' z
  have a := thru_sv hst H (𝟙 _) ((Category.id_comp _).trans h₁.symm) ((Category.id_comp _).trans h₃.symm) z hJ hJ'
  refine a.trans ?_
  rw [(cmb_iff hL' b' _ t).1 hc' _ H z J' hJ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have d := thru_sv (hb i) H (h ▷ G).left (by rw [wh_fst, ← h₁]; simp only [Category.assoc]) (by rw [wh_snd, h₃]) z hJ hJ'
  rw [mul_left_comm, ← d, gT_comp, Category.assoc, h₁]
  exact congrArg₂ (· * ·) (gs_top _ _ _).symm rfl

theorem appTop_fnR {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (c : R) :
    (spMap y).appTop.hom (fnR c) = fnR (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  intro Z G₀ _ L₀ hL R _ _ x A φ w gp hw F _ _ k
  refine ⟨fun T p hp s => existsUnique_thru (T' := TFK (R := R) F) gp.1.w hw hL A.isLB hp s,
    fun R' _ y T h ga e n b c s bF t hl hb ht j => ?_, fun K _ y ga e n τ τF hB hτ t => ?_⟩
  · have := cmb_of_lin (T' := TFK (R := R) F) (T₁ := Over.mk y) (g := spMap ga) gp.1.w hL A.isLB e rfl hl hb ht j
    exact this.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => liftFun A.A _ q * (bF i).f j) (appTop_fnR ga (c i)))
  · obtain ⟨c, hc, hu⟩ := basis_thru (T' := TFK (R := R) F) (T₁ := Over.mk (jFK (R := R) F ≫ x)) (g := 𝟙 (Sp F))
      (p := 𝟙 (Sp F)) gp.1 hw hL A.isLB (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _).symm (hB F ga _ e) hτ t
    let ε := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm
    refine ⟨fun i => ε.symm (c i), fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_), fun a ha => funext fun i => ?_⟩
    · exact congrArg (fun q => liftFun A.A _ q * (τF i).f j) (ε.apply_symm_apply (c i)).symm
    · exact ε.eq_symm_apply.2 (congrFun (hu (fun i => ε (a i)) ha) i)

end GlobalTheory.OneBasis.Calc
end
end
