module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2714
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
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
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

theorem vs_iff_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (ψ : FractionRing R →+* FractionRing Ω) (ξ : Sp (FractionRing Ω) ⟶ P.A.A.left), (∀ r, ψ (algebraMap R (FractionRing R) r) = algebraMap Ω (FractionRing Ω) (φ r)) → ξ ≫ P.A.A.hom = spMap ψ → ξ ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) = spMap (algebraMap Ω (FractionRing Ω)) ≫ x' → (∀ O (f : Γ(P.A.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∃ (j₀ : P.A.L.ι) (q : FractionRing Ω), ⊤ ≤ ξ ⁻¹ᵁ P.A.L.U j₀ ∧ q ≠ 0 ∧ ∀ (k : ℕ) (s : FractionRing Ω), 1 ≤ k → (GlobalTheory.HeatSym.VS φ t.PP.L x' g k s ↔ ∃ σ : SecM (𝟙 P.A.A.left) P.A.L k, s = q ^ k * valR ξ _ (σ.f fun _ => j₀)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ n v' D Ω _ _ _ φ x' δ dd' _ hx' _ _ _ _
  rw [← P.bundle]
  intro g hg δL _ ψ ξ hψ hξA hξx _
  obtain ⟨w, hw⟩ := P.U.ext
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.inv_hom_id]; rfl
  have hig : P.U.gen.hom.left ≫ P.U.gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, P.U.gen.hom_inv_id]; rfl
  have hξ1 : (ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left = ξ := by
    rw [Category.assoc, hgi, Category.comp_id]
  have hξ2 : (ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R) =
      spMap (algebraMap Ω (FractionRing Ω)) ≫ x' := by
    rw [Category.assoc]; exact hξx
  have chart : ∀ {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (L : LB Z), L.IsLB →
      ∀ (x : Sp A ⟶ Z), ∃ j, ⊤ ≤ x ⁻¹ᵁ L.U j := by
    intro A _ _ Z L hL x
    have hc : x (IsLocalRing.closedPoint A) ∈ (⨆ i, L.U i : Z.Opens) := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    exact ⟨j, (GlobalTheory.ZH.CrdCalc.top_le_iff x _).2 hj⟩
  obtain ⟨j₀, hj₀⟩ := chart P.A.L P.A.isLB ξ
  obtain ⟨i, hi⟩ := chart P.U.LG.L P.U.LG.isLB x'
  have hiK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) ⁻¹ᵁ P.U.LG.L.U i := by
    rw [hξ2]; exact fun p _ => hi (Set.mem_univ _)
  have hjK : ⊤ ≤ ((ξ ≫ P.U.gen.inv.left) ≫ P.U.gen.hom.left) ⁻¹ᵁ P.A.L.U j₀ := by
    rw [hξ1]; exact hj₀
  have hW : ⊤ ≤ (ξ ≫ P.U.gen.inv.left) ⁻¹ᵁ
      (LB.div (P.U.LG.L.pull (pullback.fst t.G.hom (jK R))) (P.A.L.pull P.U.gen.hom.left)).U
        (fun _ => i, fun _ => j₀) :=
    fun p hp => ⟨Set.mem_iInter.2 fun _ => hiK hp, Set.mem_iInter.2 fun _ => hjK hp⟩
  have hG : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ (LB.LinComb P.U.LG.L (fun _ : PUnit => x' ≫ 𝟙 t.G.left) (fun _ => 1)).U (fun _ => i) :=
    fun p hp => Set.mem_iInter.2 fun _ => hi hp
  set e₀ : Ω := valR (𝟙 (Sp Ω)) _ (g.s fun _ => i).val with he₀
  set W : FractionRing Ω := valR (ξ ≫ P.U.gen.inv.left) _ (w.s (fun _ => i, fun _ => j₀)).val with hWdef
  have he₀u : IsUnit e₀ := by
    rw [he₀, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hG]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hG).toMonoidHom (g.s fun _ => i)).isUnit
  have hWu : IsUnit W := by
    rw [hWdef, GlobalTheory.ZH.CrdCalc.valR_eq _ _ hW]
    exact (Units.map (GlobalTheory.ZH.CrdCalc.valHom _ _ hW).toMonoidHom (w.s (fun _ => i, fun _ => j₀))).isUnit
  have hι0 : algebraMap Ω (FractionRing Ω) e₀ ≠ 0 := (he₀u.map _).ne_zero
  have hφne : ∀ r : R, r ≠ 0 → algebraMap Ω (FractionRing Ω) (φ r) ≠ 0 := by
    intro r hr
    rw [← hψ]
    exact (map_ne_zero ψ).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  refine ⟨j₀, W * (algebraMap Ω (FractionRing Ω) e₀)⁻¹, hj₀, mul_ne_zero hWu.ne_zero (inv_ne_zero hι0), ?_⟩
  intro k s hk

  have htop : ∀ {Y : Scheme.{0}} (a : Γ(Y, ⊤)), resTop (⊤ : Y.Opens) a = a := by
    intro Y a
    have e : (homOfLE le_top : (⊤ : Y.Opens) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    simp only [resTop, e, op_id, CategoryTheory.Functor.map_id]
    rfl
  have v1 := fun σ ω hv => GlobalTheory.T.pointValue_section_in_chart_of_frame_value t.G.left P.U.LG.L P.U.LG.isLB Ω x' g k σ ω hv i hi
  have v5 : ∀ σ : SecM (𝟙 t.G.left) P.U.LG.L k,
      valR ((ξ ≫ P.U.gen.inv.left) ≫ pullback.fst t.G.hom (jK R)) _ (σ.f fun _ => i) =
        algebraMap Ω (FractionRing Ω) (valR x' _ (σ.f fun _ => i)) := by
    intro σ
    rw [hξ2]
    exact (GlobalTheory.ZH.CrdCalc.valR_spMap _ x' ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => 𝟙 t.G.left) (fun _ => (k : ℤ))).U fun _ => i) (fun p hp => Set.mem_iInter.2 fun _ => hi hp)).2 _
  have hj₀' : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb P.A.L (K := Fin 1) (fun _ => 𝟙 P.A.A.left) (fun _ => (k : ℤ))).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => hj₀ hp
  constructor
  · rintro ⟨r, σ, ω, hr, hv, hs⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_pullback_power_bundle_scalar_one _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ
    obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.exists_section_power_through_genIso_and_schemeIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB P.U.gen.inv.left hgi hig k s₁
    obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_section_power_mul_global_function _ P.A.L k σ₀ (scal P.A.A.hom (algebraMap R (FractionRing R) r)⁻¹)
    refine ⟨σ', ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ 1 hs₁ (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ₀ s₁ hσ₀
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have e4 : valR ξ _ (σ'.f fun _ => j₀) = (algebraMap Ω (FractionRing Ω) (φ r))⁻¹ * valR ξ _ (σ₀.f fun _ => j₀) := by
      erw [hσ' (fun _ => j₀)]
      rw [GlobalTheory.ZH.CrdCalc.valR_mul _ _ hj₀', GlobalTheory.ZH.FormCount.valR_scal ψ ξ _ hξA _ hj₀', map_inv₀, hψ]
    have e1' : valR (ξ ≫ P.U.gen.inv.left) ⊤ 1 = 1 := by
      rw [GlobalTheory.ZH.CrdCalc.valR_eq _ _ le_top, map_one]
    rw [v5, e1, e1', _root_.one_mul, e3] at e2
    rw [e4]
    have hr' := hφne r hr
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    have hk0 : algebraMap Ω (FractionRing Ω) e₀ ^ k ≠ 0 := pow_ne_zero _ hι0
    field_simp
    linear_combination (-(algebraMap Ω (FractionRing Ω) e₀ ^ k)) * hs + e2
  · rintro ⟨σ', rfl⟩
    obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.exists_section_power_through_generating_lineBundleIso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w hw P.A.isLB
      P.U.LG.isLB k σ'
    obtain ⟨F, hF, -⟩ := (P.U.expand k hk).1 s₁
    obtain ⟨r, hr, σ, f, hsc, -⟩ := hF
    obtain ⟨ω, hv⟩ := GlobalTheory.HeatV.exists_isValue t.G.left P.U.LG.L P.U.LG.isLB Ω x' g hg k σ
    refine ⟨r, σ, ω, hr, hv, ?_⟩
    have e1 := v1 σ ω hv
    have e2 := GlobalTheory.T.pointValue_of_section_pullback_scalar_multiple _ _ P.U.LG.L (pullback.fst t.G.hom (jK R)) k σ s₁ _ hsc (FractionRing Ω) _ i hiK
    have e3 := GlobalTheory.T.pointValue_relation_sections_through_generating_iso _ _ _ P.A.L P.U.LG.L P.U.gen.hom.left (pullback.fst t.G.hom (jK R)) w k σ' s₁ hs₁
      (FractionRing Ω) (ξ ≫ P.U.gen.inv.left) i j₀ hiK hjK
    rw [hξ1] at e3
    have hq : (ξ ≫ P.U.gen.inv.left) ≫ pullback.snd t.G.hom (jK R) ≫ jK R =
        spMap ((algebraMap Ω (FractionRing Ω)).comp φ) := by
      rw [← pullback.condition, ← Category.assoc, hξ2, Category.assoc, hx', spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have e5 : valR (ξ ≫ P.U.gen.inv.left) ⊤ (scal (pullback.snd t.G.hom (jK R) ≫ jK R) r) =
        algebraMap Ω (FractionRing Ω) (φ r) := by
      have := GlobalTheory.ZH.FormCount.valR_scal ((algebraMap Ω (FractionRing Ω)).comp φ) (ξ ≫ P.U.gen.inv.left) _ hq ⊤ le_top r
      rw [htop] at this
      exact this
    rw [v5, e1, e5, e3] at e2
    rw [map_mul, map_pow] at e2
    rw [_root_.mul_pow, inv_pow]
    field_simp
    linear_combination e2

end GlobalTheory.HeatSym
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

theorem exists_objMap_cancel_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : ∃ m₁ : ObjMap o₁ o₂ f, m₁.φ ≫ m₂.φ = m.φ := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := MapComp.exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := MapComp.isSquare_unique m.sq (hφ ▸ MapComp.isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (MapComp.lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }, hφ⟩

theorem classify_equivariant : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
  (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)), HarrisTaylorSymplecticLevelFamilyUniversalProperty b N h M s s₁ u lev →
  ∀ (ρ : sympSimGrp h M → (X ⟶ X)), SympActs s s₁ u lev ρ →
  ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)), (∀ a, ρ a ≫ s₁ = s₁ ≫ spMap (σ a)) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (Y : Over S) (t₁ : Y.left ⟶ Sp (cycAway M))
    (lu : (Fin h ⊕ Fin h → ℤ) → (Y ⟶ o.A)) (o' : Obj b N (Y.hom ≫ t)) (m : ObjMap o' o Y.hom)
    (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y.left) ⟶ o'.A)), (∀ a, (lv' a).left ≫ m.φ = (lu a).left) →
    (∀ a, IsSympLev o'.P h M (zetaAway M) (t₁ ≫ spMap (σ a)) (sympTwist a lv')) →
    ∀ (y : Y.left ⟶ X) (my : ObjMap o' u y), (∀ a, (lv' a).left ≫ my.φ = y ≫ (lev a).left) →
    y ≫ s = Y.hom ≫ t → y ≫ s₁ = t₁ →
    ∀ (r : sympSimGrp h M → (Y ⟶ Y)), (∀ a, (r a).left ≫ t₁ = t₁ ≫ spMap (σ a)) →
    (∀ a c, r a ≫ lu c = sympTwist a lu c) → ∀ a, (r a).left ≫ y = y ≫ ρ a := by
  intro p _ D R _ b N h M X s s₁ u lev hU ρ hρ σ hσ S t o Y t₁ lu o' m lv' hlv' hlev y my hmy hys hys₁ r hrt hr a
  let compObj : ∀ {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
      {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃},
      ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → ObjMap o₁ o₃ (f ≫ g) := by
    intro S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₁ m₂
    exact { φ := m₁.φ ≫ m₂.φ
            φ₂ := m₁.φ₂ ≫ m₂.φ₂
            cart := m₁.cart.comp m₂.cart
            sq := MapComp.isSquare_comp m₁.sq m₂.sq
            act := fun c => by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
            pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
              (MapComp.lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
            eta := fun c => by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc] }
  have cast : ∀ {f f' : Y.left ⟶ S} (_ : f = f') (m₀ : ObjMap o' o f), ∃ m' : ObjMap o' o f', m'.φ = m₀.φ := by
    intro f f' e m₀; subst e; exact ⟨m₀, rfl⟩
  have hrY : (r a).left ≫ Y.hom = Y.hom := Over.w (r a)
  obtain ⟨ma, hma⟩ := (hρ a).2.2

  have h₁ : (y ≫ ρ a) ≫ s = Y.hom ≫ t ∧ (y ≫ ρ a) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u (y ≫ ρ a), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = (y ≫ ρ a) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, (hρ a).1, hys], by rw [Category.assoc, hσ, ← Category.assoc, hys₁],
      compObj my ma, fun c => ?_⟩
    have e₁ := hmy (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M c)))
    have e₂ := hma c
    simp only [sympTwist] at e₂ ⊢
    dsimp [compObj]
    change _ ≫ my.φ ≫ ma.φ = _
    rw [← Category.assoc, e₁, Category.assoc, e₂, Category.assoc]

  obtain ⟨mr, hmr⟩ := cast hrY.symm m
  obtain ⟨m₂, hφ⟩ := exists_objMap_cancel_φ mr m
  rw [hmr] at hφ
  have hpull : ∀ c, (sympTwist a lv' c).left ≫ m₂.φ = (r a).left ≫ (lv' c).left := by
    intro c
    apply m.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, hlv' c]
      simp only [sympTwist] at hlv' ⊢
      rw [hlv', ← Over.comp_left, hr a c]
      rfl
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (sympTwist a lv' c), Category.assoc,
        Over.w (lv' c)]
      simp
  have h₂ : ((r a).left ≫ y) ≫ s = Y.hom ≫ t ∧ ((r a).left ≫ y) ≫ s₁ = t₁ ≫ spMap (σ a) ∧
      ∃ m' : ObjMap o' u ((r a).left ≫ y), ∀ c, (sympTwist a lv' c).left ≫ m'.φ = ((r a).left ≫ y) ≫ (lev c).left := by
    refine ⟨by rw [Category.assoc, hys, ← Category.assoc, hrY], by rw [Category.assoc, hys₁, hrt],
      compObj m₂ my, fun c => ?_⟩
    dsimp [compObj]
    change _ ≫ m₂.φ ≫ my.φ = _
    rw [← Category.assoc, hpull c, Category.assoc, hmy c, Category.assoc]
  exact (hU Y.left (Y.hom ≫ t) (t₁ ≫ spMap (σ a)) o' (sympTwist a lv') (hlev a)).unique h₂ h₁

end GlobalTheory.HTSympCover
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

abbrev sqR (N : Near π G) : Over (Sp R) :=
  Over.mk ((Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π)

def fstU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))))))

def sndU (N : Near π G) : sqR N ⟶ N.U :=
  Over.homMk ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _)
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w (snd (Desc.UT N) (Desc.UT N)))))))

def pairU (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  (lift (fstU N) (sndU N)).left

abbrev VT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) : (Desc.UT N ⊗ Desc.UT N).left.Opens :=
  pairU N ⁻¹ᵁ V

theorem pairU_over (N : Near π G) :
    pairU N ≫ (N.U ⊗ N.U).hom = (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π :=
  Over.w (lift (fstU N) (sndU N))

def mT (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : (VT N V).toScheme ⟶ (Desc.UT N).left :=
  pullback.lift ((pairU N ∣_ V) ≫ m) ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) (by
    have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
    refine (Category.assoc _ _ _).trans ?_
    rw [hm, ← Category.assoc, e, Category.assoc, pairU_over, Category.assoc])

variable [GrpObj G]

def trip (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N ⟶ (Over.pullback p).obj G := by
  letI : (Over.pullback p).Monoidal := (Over.instBraidedPullback (f := p)).toMonoidal
  letI : GrpObj ((Over.pullback p).obj G) := Functor.grpObjObj (F := Over.pullback p) (G := G)
  exact (snd _ _ ≫ Desc.emb N p hp)⁻¹ * (fst _ _ ≫ Desc.sum N p hp)

def Pk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Over (pullback π π) :=
  Over.mk (pullback.snd (Desc.emb N p hp).left (trip N p hp).left ≫ ((Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N).hom)

def dP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.fst _ _) (by
    show pullback.fst _ _ ≫ (Desc.UT N).hom = pullback.snd _ _ ≫ _
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, pullback.condition, Category.assoc, Over.w (trip N p hp)])

def abP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (fst (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) : Pk N p hp ⟶ Desc.UT N :=
  Over.homMk (pullback.snd _ _ ≫ (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)).left)
    ((Category.assoc _ _ _).trans (congrArg (pullback.snd _ _ ≫ ·) (Over.w (snd (Desc.UT N ⊗ Desc.UT N) (Desc.UT N)))))

def cdP (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ Desc.UT N ⊗ Desc.UT N :=
  lift (cP N p hp) (dP N p hp)

def Wk (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (V : (N.U ⊗ N.U).left.Opens) :
    (Pk N p hp).left.Opens :=
  (abP N p hp).left ⁻¹ᵁ VT N V ⊓ (cdP N p hp).left ⁻¹ᵁ VT N V

def q3 (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Pk N p hp ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N :=
  Over.homMk (pullback.snd _ _) rfl

theorem abP_eq (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp = q3 N p hp ≫ fst _ _ := Over.OverMorphism.ext rfl

theorem indicatorIdempotent_eq_add_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    cP N p hp = q3 N p hp ≫ snd _ _ := Over.OverMorphism.ext rfl

theorem dP_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    dP N p hp ≫ Desc.emb N p hp = q3 N p hp ≫ trip N p hp := Over.OverMorphism.ext pullback.condition

theorem abP_sum (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    abP N p hp ≫ Desc.sum N p hp = cdP N p hp ≫ Desc.sum N p hp := by
  letI : (Over.pullback p).Monoidal := (Over.instBraidedPullback (f := p)).toMonoidal
  letI : GrpObj ((Over.pullback p).obj G) := Functor.grpObjObj (F := Over.pullback p) (G := G)
  have e4 : cdP N p hp ≫ Desc.sum N p hp = (cP N p hp ≫ Desc.emb N p hp) * (dP N p hp ≫ Desc.emb N p hp) := by
    rw [cdP, Desc.sum, comp_mul, ← Category.assoc, lift_fst, ← Category.assoc, lift_snd]
  rw [e4, dP_emb, trip, comp_mul, GrpObj.comp_inv, indicatorIdempotent_eq_add_sum, abP_eq]
  simp only [Category.assoc]
  exact (mul_inv_cancel_left _ _).symm

theorem exists_lift (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (Z : Scheme.{0})
    (g g' : Z ⟶ (Desc.UT N ⊗ Desc.UT N).left) (h : g ≫ (Desc.sum N p hp).left = g' ≫ (Desc.sum N p hp).left) :
    ∃ z : Z ⟶ (Pk N p hp).left, z ≫ (abP N p hp).left = g ∧ z ≫ (cdP N p hp).left = g' := by
  letI : (Over.pullback p).Monoidal := (Over.instBraidedPullback (f := p)).toMonoidal
  letI : GrpObj ((Over.pullback p).obj G) := Functor.grpObjObj (F := Over.pullback p) (G := G)
  let FinalForm : Over (pullback π π) := Over.mk (g ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  have hw : g' ≫ (Desc.UT N ⊗ Desc.UT N).hom = g ≫ (Desc.UT N ⊗ Desc.UT N).hom := by
    rw [← Over.w (Desc.sum N p hp), ← Category.assoc, ← h, Category.assoc]
  let a : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g rfl
  let b : FinalForm ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk g' hw
  have hab : a ≫ Desc.sum N p hp = b ≫ Desc.sum N p hp := Over.OverMorphism.ext h
  let t : FinalForm ⟶ (Desc.UT N ⊗ Desc.UT N) ⊗ Desc.UT N := lift a (b ≫ fst _ _)
  have ht : (b ≫ snd _ _) ≫ Desc.emb N p hp = t ≫ trip N p hp := by
    rw [trip, comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_snd, ← Category.assoc t, lift_fst, hab, Desc.sum,
      comp_mul]
    simp only [Category.assoc]
    exact (inv_mul_cancel_left _ _).symm
  let zo : FinalForm ⟶ Pk N p hp := Over.homMk (pullback.lift (b ≫ snd _ _).left t.left (congrArg Over.Hom.left ht))
    (by show pullback.lift _ _ _ ≫ pullback.snd _ _ ≫ _ = _
        rw [← Category.assoc, pullback.lift_snd]; exact Over.w t)
  have h1 : zo ≫ abP N p hp = a := by rw [abP_eq, ← Category.assoc]; exact (congrArg (· ≫ fst _ _)
    (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_fst _ _)
  have h2 : zo ≫ cdP N p hp = b := by
    have hc : zo ≫ cP N p hp = b ≫ fst _ _ := by
      rw [indicatorIdempotent_eq_add_sum, ← Category.assoc]; exact (congrArg (· ≫ snd _ _)
        (Over.OverMorphism.ext (pullback.lift_snd _ _ _) : zo ≫ q3 N p hp = t)).trans (lift_snd _ _)
    have hd : zo ≫ dP N p hp = b ≫ snd _ _ := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    rw [cdP, comp_lift, hc, hd]
    exact (lift_comp_fst_snd b)
  exact ⟨zo.left, congrArg Over.Hom.left h1, congrArg Over.Hom.left h2⟩

end GlobalTheory.Mum.DescKP
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Desc

theorem surjective_U_hom {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} (hπ : Surjective π)
    {G' : Over S} [GrpObj G'] (N : Near π G') : Surjective N.U.hom := by
  have := N.smooth
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  let e : S ⟶ G'.left := (1 : Over.mk (𝟙 S) ⟶ G').left
  have he : e ≫ G'.hom = 𝟙 S := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
  have hes : G'.hom (e s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨z, hz⟩ : e s ∈ Set.range N.u := N.all _ (by rw [hes]; exact hs)
  have hzs : pullback.snd N.U.hom π z = s := by
    rw [← N.u_over, Scheme.Hom.comp_apply, hz, hes]
  have hc : closedPoint R ∈ Set.range N.U.hom := ⟨pullback.fst N.U.hom π z, by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hzs, hs]⟩
  exact ⟨fun x => (Flat.generalizingMap N.U.hom).stableUnderGeneralization_range
    (IsLocalRing.specializes_closedPoint x) hc⟩

theorem surjective_UT_hom : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), Surjective π →
    ∀ (G' : Over S) [GrpObj G'] (N : Near π G'), Surjective (Desc.UT N).hom := by
  intro R _ _ S π hπ G' _ N
  have := surjective_U_hom hπ N
  exact inferInstanceAs (Surjective (pullback.snd N.U.hom (pullback.fst π π ≫ π)))

end GlobalTheory.Mum.Desc
end
