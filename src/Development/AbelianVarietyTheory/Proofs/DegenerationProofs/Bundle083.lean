module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle072
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle073
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsReg
open GlobalTheory.Points

theorem valR_appIso_inv {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (U : X.Opens) (f : Γ(X, U))
    {C : Type} [CommRing C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    valR (y ≫ j) (j ''ᵁ U) ((j.appIso U).inv.hom f) = valR y U f := by
  rw [← valR_appLE y j (j.preimage_image_eq U).ge hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res y le_rfl hy f

theorem valR_valueAt {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ) [GrpObj A] {T : Over B}
    {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [CommRing K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) = valR x ⊤ v * valR x _ (τ.s fun _ => j).val := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  exact e

theorem range_subset {K : Type} [Field K] {X : Scheme.{0}} (x : Sp K ⟶ X) {U : X.Opens} (p : Sp K) (h : x p ∈ U) :
    Set.range x ⊆ U := by
  rintro _ ⟨y, rfl⟩
  rw [Subsingleton.elim y p]
  exact h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} (Q : ZHPre ρ M U₀)

theorem exists_eq_mul_unit (hne : (U₀ : Set M.Z).Nonempty) {N : M.Z.Opens} {σ : Q.SecFam N} {c : Ω}
    (hσ : Q.ThMul c N σ) {a : S.Gam} {W : M.Z.Opens} {h : W.toScheme ⟶ Q.G.left} {w : W.toScheme}
    (hE : Q.ExtPt a W h) (hF : Q.FrameUnit a W h w) (hw : W.ι w ∈ N) (jL : Q.L.L.ι) (hj : h w ∈ Q.L.L.U jL) :
    ∃ (T : M.Z.Opens) (f : Γ(M.Z, T)) (e : Ω), W.ι w ∈ T ∧ e ≠ 0 ∧ e ∈ M.O (W.ι w) ∧ e⁻¹ ∈ M.O (W.ι w) ∧
      c * S.th a = valF M.pt T f * e⁻¹ ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), Set.range y = {w} →
        valF (y ≫ W.ι) T f = valF (y ≫ h) _ (σ fun _ => jL) := by
  let V : W.toScheme.Opens := h ⁻¹ᵁ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL)
  have hwV : w ∈ V := by
    refine ⟨?_, Set.mem_iInter.2 fun _ => hj⟩
    change (h ≫ Q.G.hom) w ∈ N
    rw [hE.1]
    exact hw
  have hT : W.ι w ∈ W.ι ''ᵁ V := ⟨w, hwV, rfl⟩
  have hval : ∀ (K : Type) [Field K] (y : Sp K ⟶ W.toScheme), ⊤ ≤ y ⁻¹ᵁ V →
      valF (y ≫ W.ι) (W.ι ''ᵁ V) ((W.ι.appIso V).inv.hom ((h.app _).hom (σ fun _ => jL))) =
        valF (y ≫ h) _ (σ fun _ => jL) := fun K _ y hy =>
    (valR_appIso_inv W.ι V _ y hy).trans (valR_comp y h _ _).symm
  have lift : ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ x : Sp Ω ⟶ U.toScheme, x ≫ U.ι = M.pt := fun U hU =>
    ⟨IsOpenImmersion.lift U.ι M.pt (by
      rw [Scheme.Opens.range_ι]
      exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hU)), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨x, hx⟩ := lift W ⟨w.1, w.2⟩
  obtain ⟨x₀, hx₀⟩ := lift U₀ hne
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  have hcond : (t₀ ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = x₀ ≫ Q.u₀ := by
    rw [Q.u₀_gen x₀ hx₀, Category.assoc, Over.w (ρ.pt a)]
    exact Category.comp_id _
  let x' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := pullback.lift _ _ hcond
  have h1 : x' ≫ pullback.fst _ _ = t₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have h2 : x' ≫ pullback.snd _ _ ≫ U₀.ι = M.pt := by
    rw [← Category.assoc, pullback.lift_snd, hx₀]
  have h3 : x' ≫ Q.φ ≫ Q.G.hom = M.pt := by
    rw [← h2]
    exact congrArg (x' ≫ ·) Q.cart.1.w
  have h4 : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx h3 h1
  have hxV : ⊤ ≤ x ⁻¹ᵁ V := by
    have h5 := M.top_le_preimage_pt ⟨_, hT⟩
    rw [← hx] at h5
    exact le_preimage_mono x (W.ι.preimage_image_eq V).le h5
  have hxh : Set.range (x' ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U fun _ => jL : Q.G.left.Opens) := by
    rw [← h4]
    exact (top_le_preimage_iff _ _).1 hxV
  obtain ⟨jP, hjP⟩ : ∃ jP, Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U jP := by
    have h5 : (t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω) ∈ ⨆ i, ρ.P.L.U i := by
      rw [ρ.P.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    exact ⟨i, range_subset _ _ hi⟩
  obtain ⟨he0, he1, he2⟩ := hF jP jL x' _ hj h3 h1 (h1 ▸ hjP) rfl
  refine ⟨_, _, _, hT, he0, he1, he2, ?_, fun K _ y hy => hval K y fun p _ => ?_⟩
  · have hr : (t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        x' ≫ pullback.fst _ _ := by
      rw [h1, Category.assoc, ← Over.comp_left, ptSecT, lift_snd]
    have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := Spec.map_id _
    have e := hσ Ω (RingHom.id Ω) x' _ jP jL (by rw [h2, hid, Category.id_comp]) hr (h1 ▸ hjP)
      (fun p hp => Set.mem_iInter.1 (hxh hp).2 0) (fun p hp => (hxh hp).1)
    have e2 := valR_valueAt ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ jP hjP
    have e3 : valR (X := (baseOver (Sp S.R)).left) t₀ ⊤ (fn (⟨S.th a, S.th_mem a⟩ : S.R)) = S.th a :=
      valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _
    rw [e3] at e2
    rw [Fintype.sum_unique, zpow_one, RingHom.id_apply, valF_eq_valR, e2, ← h4, ← hval Ω x hxV, hx] at e
    have hn := (div_ne_zero_iff.1 he0).1
    rw [inv_div, ← mul_div_assoc, eq_div_iff hn, _root_.mul_assoc, _root_.mul_comm (valF M.pt _ _)]
    exact e
  · have h5 : y p ∈ Set.range y := ⟨p, rfl⟩
    rw [hy] at h5
    change y p ∈ V
    rw [show y p = w from h5]
    exact hwV

end GlobalTheory.ZH.TorsReg


open GlobalTheory.Points GlobalTheory.ZH.TorsReg in
theorem GlobalTheory.ZH.mul_theta_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (c : Ω), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w → W.ι w ∈ N → c * S.th a ∈ M.O (W.ι w) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (j : Q.LOne.ι), Set.range x = {w} → valF (x ≫ h) _ (σ j) ≠ 0 → c * S.th a ≠ 0 ∧ (c * S.th a)⁻¹ ∈ M.O (W.ι w) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N σ c _ hσ a W h w hE hF hw
  constructor
  · have h5 : h w ∈ ⨆ i, Q.L.L.U i := by
      rw [Q.L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h5
    obtain ⟨T, f, e, hT, -, -, he, hc, -⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [hc]
    exact mul_mem (RatModel.valF_mem_O hT f) he
  · intro K _ x j hx hv
    have hxw : x (IsLocalRing.closedPoint K) = w := by
      have h5 : x (IsLocalRing.closedPoint K) ∈ Set.range x := ⟨_, rfl⟩
      rwa [hx] at h5
    obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim k 0)⟩
    have hi : h w ∈ Q.L.L.U i := by
      by_contra hi
      refine hv (dif_neg fun hle => hi ?_)
      rw [← hxw]
      exact Set.mem_iInter.1 (hle (x := IsLocalRing.closedPoint K) trivial).2 0
    obtain ⟨T, f, e, hT, he0, he1, -, hc, hK⟩ := GlobalTheory.ZH.TorsReg.exists_eq_mul_unit Q hO.ne hσ hE hF hw i hi
    rw [← hK K x hx] at hv
    have hxw' : (x ≫ W.ι) (IsLocalRing.closedPoint K) = W.ι w := by rw [← hxw]; rfl
    have hle : ⊤ ≤ (x ≫ W.ι) ⁻¹ᵁ T := (GlobalTheory.Points.le_preimage_iff _ _).2 (hxw' ▸ hT)
    have hb : W.ι w ∈ M.Z.basicOpen f :=
      hxw' ▸ (GlobalTheory.Points.le_preimage_iff _ _).1 ((GlobalTheory.Points.le_preimage_basicOpen_iff _ hle f).2 (isUnit_iff_ne_zero.2 hv))
    obtain ⟨hf0, hf1⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hT f).2 hb)
    rw [hc]
    refine ⟨mul_ne_zero hf0 (inv_ne_zero he0), ?_⟩
    rw [_root_.mul_inv, inv_inv]
    exact mul_mem hf1 he1

end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem extPt_comp_eq_integral_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∀ (F : u.G.left ⟶ Q.G.left) (ψ : pullback u.G.hom (jK u.V) ⟶ pullback ρ.P.A.hom Q.u₀), Q.TestMap u yV yK F ψ → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left), Q.ExtPt a W h → ∀ (hV : Sp u.V ⟶ u.G.left) (x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V)), (hV ≫ u.G.hom = 𝟙 _ ∧ x ≫ pullback.fst _ _ = jK u.V ≫ hV ∧ x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left) → ∀ yW : Sp u.V ⟶ W.toScheme, yW ≫ W.ι = yV → yW ≫ h = hV ≫ F := by
  intro o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT F ψ hM a W h hE hV x hx yW hyW
  obtain ⟨-, -, hK, hK0⟩ := hT
  obtain ⟨hF, hψ1, hψ2, hψ3⟩ := hM
  obtain ⟨hh, hE⟩ := hE
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
  have hφ : Q.φ ≫ Q.G.hom = pullback.snd ρ.P.A.hom Q.u₀ ≫ U₀.ι := Q.cart.1.w
  have hFw : F ≫ Q.G.hom = u.G.hom ≫ yV := hF.1.w
  let sec : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
    pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
      rw [Category.assoc, hpa]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have hs1 : sec ≫ pullback.fst _ _ = Q.u₀ ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
  have hs2 : sec ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hs3 : sec ≫ Q.φ ≫ Q.G.hom = U₀.ι := by
    rw [hφ, ← Category.assoc, hs2, Category.id_comp]
  let N : M.Z.Opens := W ⊓ U₀
  let iW : N.toScheme ⟶ W.toScheme := M.Z.homOfLE inf_le_left
  let iU : N.toScheme ⟶ U₀.toScheme := M.Z.homOfLE inf_le_right
  have hiW : iW ≫ W.ι = N.ι := M.Z.homOfLE_ι _
  have hiU : iU ≫ U₀.ι = N.ι := M.Z.homOfLE_ι _
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [← hyW]
      exact (yW (jK u.V w)).2
    · rw [← hK]
      exact (yK w).2
  let k : Sp (FractionRing u.V) ⟶ N.toScheme := IsOpenImmersion.lift N.ι (jK u.V ≫ yV) hr
  have hk : k ≫ N.ι = jK u.V ≫ yV := IsOpenImmersion.lift_fac _ _ _
  have hkW : k ≫ iW = jK u.V ≫ yW := by
    rw [← cancel_mono W.ι, Category.assoc, hiW, hk, Category.assoc, hyW]
  have hkU : k ≫ iU = yK := by
    rw [← cancel_mono U₀.ι, Category.assoc, hiU, hk, hK]
  have hne : (N : Set M.Z).Nonempty :=
    ⟨_, (k (IsLocalRing.closedPoint (FractionRing u.V))).2⟩
  have hg : Set.range M.pt ⊆ Set.range N.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let g : Sp Ω ⟶ N.toScheme := IsOpenImmersion.lift N.ι M.pt hg
  have hgN : g ≫ N.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have : IsDominant (g ≫ N.ι) := by rw [hgN]; infer_instance
  have : IsDominant g := IsDominant.of_comp_of_isOpenImmersion g N.ι
  have key : iW ≫ h = iU ≫ sec ≫ Q.φ := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ g ?_
    · simp only [Category.assoc]
      rw [hh, hs3, hiW, hiU]
    · have h1 : (g ≫ iU) ≫ U₀.ι = M.pt := by rw [Category.assoc, hiU, hgN]
      have := hE (g ≫ iW) (g ≫ iU ≫ sec) (by rw [Category.assoc, hiW, hgN])
        (by simp only [Category.assoc]; rw [hs3, hiU, hgN])
        (by
          simp only [Category.assoc]
          rw [hs1, ← Q.u₀_gen _ h1]
          simp only [Category.assoc])
      simpa only [Category.assoc] using this
  have hxψ : yK ≫ sec = x ≫ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hs1, Category.assoc, hψ1, ← Category.assoc, hK0]
      exact hx4.symm
    · rw [Category.assoc, hs2, Category.assoc, hψ2, ← Category.assoc, hx3, Category.comp_id, Category.id_comp]
  have : IsDominant (jK u.V) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective u.V (FractionRing u.V))]
      exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ (jK u.V) ?_
  · simp only [Category.assoc]
    rw [hh, hyW, hFw, ← Category.assoc, hx1, Category.id_comp]
  · rw [← Category.assoc, ← hkW, Category.assoc, key, ← Category.assoc, hkU, ← Category.assoc, hxψ,
      Category.assoc, hψ3, ← Category.assoc, hx2, Category.assoc]

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH

theorem exists_iso_of_existsUnique_ext {B B' : Scheme.{0}} (j : B' ⟶ B) (G G' : Over B) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hext : ∀ (G G' : Over B) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f)
    (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj G') (he : IsMonHom e.hom) :
    ∃ E : G ≅ G', IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hext G G' hG hG' e.hom he
  obtain ⟨b, ⟨hb, hb'⟩, -⟩ := hext G' G hG' hG e.inv inferInstance
  refine ⟨⟨a, b, ?_, ?_⟩, ha, ha'⟩
  · exact (hext G G hG hG (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (hext G' G' hG' hG' (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, ha', hb', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

theorem ZHPre.exists_testMap : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (jV : u.V →+* OO p) (yV : Sp u.V ⟶ M.Z) (yK : Sp (FractionRing u.V) ⟶ U₀.toScheme), Q.TestFac y u jV yV yK → ∃ F ψ, Q.TestMap u yV yK F ψ := by
  intro hext o Ω _ _ _ _ S ρ M U₀ Q p _ y y₀ u jV yV yK hT
  obtain ⟨-, -, h₁, h₂⟩ := hT
  have := u.U.gen_hom
  have gp₁ : IsGrpPullback ((Over.pullback (jK u.V)).obj u.G) ρ.P.A (spMap u.yK) (u.U.gen.hom.left ≫ u.φ) :=
    ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  have gp₂ := ((isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK).comp
    (isGrpPullback_pullback ρ.P.A Q.u₀)).congr h₂ rfl
  obtain ⟨e₁, m₁, he₁⟩ := grpPullback_iso gp₁ gp₂
  have gp₃ := ((((isGrpPullback_of_iso e₁).comp
    (isGrpPullback_pullback ((Over.pullback Q.u₀).obj ρ.P.A) yK)).congr (Category.id_comp _) rfl).comp Q.cart).congr h₁ rfl
  have gp₄ := (isGrpPullback_pullback ((Over.pullback yV).obj Q.G) (jK u.V)).comp (isGrpPullback_pullback Q.G yV)
  obtain ⟨e₂, m₂, he₂⟩ := grpPullback_iso gp₃ gp₄
  obtain ⟨E, mE, hE⟩ := exists_iso_of_existsUnique_ext (jK u.V) u.G ((Over.pullback yV).obj Q.G) u.semi
    (IsSemiAbelian.pullback _ Q.G Q.semi) (fun G G' _ _ => hext u.V (FractionRing u.V) G G') e₂ m₂
  refine ⟨E.hom.left ≫ pullback.fst Q.G.hom yV,
    e₁.hom.left ≫ pullback.fst ((Over.pullback Q.u₀).obj ρ.P.A).hom yK,
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback Q.G yV)).congr (Category.id_comp _) rfl, ?_, ?_, ?_⟩
  · exact (Category.assoc _ _ _).trans he₁
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (e₁.hom.left ≫ ·) (pullback.condition (f := ((Over.pullback Q.u₀).obj ρ.P.A).hom) (g := yK))).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ yK) (Over.w e₁.hom))
  · refine he₂.symm.trans ?_
    have a : ((Over.pullback (jK u.V)).map E.hom).left ≫ pullback.fst ((Over.pullback yV).obj Q.G).hom (jK u.V) =
        pullback.fst u.G.hom (jK u.V) ≫ E.hom.left := pullback.lift_fst _ _ _
    rw [← hE]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst Q.G.hom yV) a).trans (Category.assoc _ _ _))

end GlobalTheory.ZH
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LocThetaConv

variable {X Y : Scheme.{0}}

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem appLE_resG (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) {U : Y.Opens} (e : U ≤ f ⁻¹ᵁ W')
    (a : Γ(X, W)) : (f.appLE W' U e).hom (resG X h a) =
      (f.appLE W U (e.trans fun _ hy => h hy)).hom a := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem resG_appLE (f : Y ⟶ X) {W : X.Opens} {U U' : Y.Opens} (h : U' ≤ U) (e : U ≤ f ⁻¹ᵁ W)
    (a : Γ(X, W)) : resG Y h ((f.appLE W U e).hom a) = (f.appLE W U' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem g_val (L : LB X) {K : Type} [Fintype K] [Subsingleton K] (φ : K → (Y ⟶ X)) (k : K)
    (i j : K → L.ι) : ((LB.LinComb L φ (fun _ => 1)).g i j).val =
      ((φ k).appLE (L.U (i k) ⊓ L.U (j k)) (LB.wchart L φ i ⊓ LB.wchart L φ j)
        (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))).hom
        (L.g (i k) (j k)).val := by
  simp only [LB.LinComb, zpow_one]
  erw [Fintype.prod_subsingleton _ k]
  rfl

theorem mem_one {L : LB X} {j : Fin 1 → L.ι} {x : X} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_pull' {L : LB X} (f : Y ⟶ X) {j : L.ι} {y : Y} :
    y ∈ (L.pull f).U (fun _ => j) ↔ f y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_secOn (L : LB X) (V : X.Opens) (σ : LB.Sec (L.pull V.ι)) :
    ∃ τ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V,
      ∀ y ∈ nonzeroLocus σ, ∃ j, V.ι y ∈ X.basicOpen (τ j) := by
  set L₁ := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1) with hL₁
  have e : ∀ j : Fin 1 → L.ι, (L.pull V.ι).U (fun _ => j 0) ≤ V.ι ⁻¹ᵁ (V ⊓ L₁.U j) :=
    fun j y hy => ⟨y.2, mem_one.2 ((mem_pull' _).1 hy)⟩
  have e' : ∀ j : Fin 1 → L.ι, V.ι ⁻¹ᵁ (V ⊓ L₁.U j) ≤ (L.pull V.ι).U (fun _ => j 0) :=
    fun j y hy => (mem_pull' _).2 (mem_one.1 hy.2)
  have hV : V ≤ V.ι.opensRange := V.opensRange_ι.ge
  choose τ hτ using fun j : Fin 1 → L.ι =>
    (bijective_appLE V.ι _ (inf_le_left.trans hV) _ (e j) (e' j)).2 (σ.f fun _ => j 0)
  refine ⟨τ, fun i j => ?_, fun y hy => ?_⟩
  · apply (bijective_appLE V.ι (V ⊓ L₁.U i ⊓ L₁.U j) ((inf_le_left.trans inf_le_left).trans hV)
      ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
      (fun y hy => ⟨e i hy.1, (e j hy.2).2⟩) (fun y hy => ⟨e' i hy.1, e' j ⟨hy.1.1, hy.2⟩⟩)).1
    have h := σ.compat (fun _ => i 0) (fun _ => j 0)
    rw [← hτ i, ← hτ j] at h
    rw [map_mul]
    refine ((appLE_resG _ _ _ _).trans (resG_appLE _ _ _ _).symm).trans (h.trans ?_)
    congr 1
    · have h1 : ((L.pull V.ι).g (fun _ => i 0) (fun _ => j 0)).val =
          (V.ι.appLE (L.U (i 0) ⊓ L.U (j 0)) ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
            (fun y hy => ⟨(mem_pull' _).1 hy.1, (mem_pull' _).1 hy.2⟩)).hom
            (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : PUnit => V.ι) PUnit.unit _ _).trans (by rfl)
      have h2 : (L₁.g i j).val = resG X (fun y hy => ⟨mem_one.1 hy.1, mem_one.1 hy.2⟩ :
          L₁.U i ⊓ L₁.U j ≤ L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : Fin 1 => 𝟙 X) 0 _ _).trans (by rfl)
      rw [h1, h2]
      exact ((appLE_resG _ _ _ _).trans (appLE_resG _ _ _ _)).symm
    · exact (resG_appLE _ _ _ _).trans (appLE_resG _ _ _ _).symm
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    have h := Scheme.basicOpen_appLE V.ι _ _ (e fun _ => k PUnit.unit) (τ fun _ => k PUnit.unit)
    have h' := hτ fun _ => k PUnit.unit
    have hk' : y ∈ V.toScheme.basicOpen (σ.f fun _ => k PUnit.unit) := hk
    rw [← h'] at hk'
    exact (h.le hk').2

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_secFam_fibNe : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q H z
  obtain ⟨N, σ, hz, hσ⟩ := H z
  obtain ⟨τ, hτ, hne⟩ := exists_secOn Q.L.L _ σ
  refine ⟨N, τ, hz, hτ, fun K _ _ x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hσ _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
  obtain ⟨j, hj⟩ := hne y hy
  have := Q.dim
  have : Smooth Q.G.hom := SmoothOfRelativeDimension.smooth S.g _
  obtain ⟨g, hg, hO⟩ := exists_point Q.G.hom x _ _ hj hyx
  exact ⟨g, j, hg, ((GlobalTheory.Points.le_preimage_basicOpen_iff g
    (GlobalTheory.Points.le_preimage_mono g (Scheme.basicOpen_le _ _) hO) (τ j)).1 hO).ne_zero⟩

end GlobalTheory.ZH.LocThetaConv
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.resG_eq_of_thMul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (σ' : Q.SecFam N') (c : Ω), Q.ThMul c N σ → Q.ThMul c N' σ' → ∀ (j : Q.LOne.ι) (O : Q.G.left.Opens) (h : O ≤ Q.G.hom ⁻¹ᵁ N ⊓ Q.LOne.U j) (h' : O ≤ Q.G.hom ⁻¹ᵁ N' ⊓ Q.LOne.U j), resG _ h (σ j) = resG _ h' (σ' j) := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO N N' σ σ' c hσ hσ' j O h h'
  obtain ⟨K, _, β, g, r, jP, h1, h2, h3, h4⟩ := Q.exists_generic hO.ne
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine eq_of_valF_generic (g ≫ Q.φ) h4 fun hm => ?_
  have hm' := (top_le_preimage_iff _ _).1 hm
  have hV : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N : Q.G.left.Opens) := fun y hy => (h (hm' hy)).1
  have hV' : Set.range (g ≫ Q.φ) ⊆ (Q.G.hom ⁻¹ᵁ N' : Q.G.left.Opens) := fun y hy => (h' (hm' hy)).1
  have hL : Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL := fun y hy => Set.mem_iInter.1 (h (hm' hy)).2 0
  have e := (hσ K β g r jP jL h1 h2 h3 hL hV).symm.trans (hσ' K β g r jP jL h1 h2 h3 hL hV')
  refine (valR_res _ h hm _).trans (Eq.trans ?_ (valR_res _ h' hm _).symm)
  refine mul_left_cancel₀ (zpow_ne_zero _ ?_) e
  refine IsUnit.ne_zero ?_
  have hw : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun w _ =>
    ⟨Set.mem_iInter.2 fun _ => h3 ⟨w, Scheme.Hom.comp_apply _ _ _⟩,
      Set.mem_iInter.2 fun _ => hL ⟨w, Scheme.Hom.comp_apply _ _ _⟩⟩
  rw [valF_eq_valR, valR_eq g _ hw]
  exact (Units.isUnit _).map _

end GlobalTheory.ZH
end
