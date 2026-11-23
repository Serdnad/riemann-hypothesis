module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle016
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twfunct

section General

variable {R : Type} [CommRing R] [IsDomain R] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {x : Spec (CommRingCat.of R) ⟶ S}

theorem exists_lift {T T' : Type} [CommGroup T] [CommGroup T'] (Γ : QFGroup R T) (Γ' : QFGroup R T')
    {N N' : ℕ} {i : Γ.G.left ⟶ G.left} {i' : Γ'.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) (h' : Γ'.IsTorsionAlong G x N' i') (hN : N ∣ N')
    (u : G ⟶ G) [IsMonHom u] : ∃ a : Γ.G ⟶ Γ'.G, a.left ≫ i' = i ≫ u.left := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, by simp [g]⟩
  obtain ⟨k, rfl⟩ := hN
  have hg' : (g ≫ u) ^ (N * k) = 1 := by
    rw [← MonObj.pow_comp, pow_mul, hg, one_pow, MonObj.one_comp]
  obtain ⟨a, ha⟩ := (h'.kernel Γ.G (g ≫ u)).1 hg'
  exact ⟨a, by rw [ha]; simp [g]⟩

theorem left_ext {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {Y : Scheme.{0}} (v w : Y ⟶ Γ.G.left) (h1 : v ≫ Γ.G.hom = w ≫ Γ.G.hom)
    (h2 : v ≫ i = w ≫ i) : v = w := by
  have := h.inj (Over.mk (w ≫ Γ.G.hom)) (Over.homMk v h1) (Over.homMk w rfl) h2
  exact congrArg (fun z => z.left) this

omit [IsDomain R] in
theorem valAt_comp {X Y : Scheme.{0}} (v : Spec (CommRingCat.of R) ⟶ X) (a : X ⟶ Y) (s : Γ(Y, ⊤)) :
    valAt v ⊤ le_top ((a.app ⊤).hom s) = valAt (v ≫ a) ⊤ le_top s :=
  Funct.valAt_pullback v a _ rfl ⊤ le_top le_top s

omit [IsDomain R] in
theorem valAt_specMap {B : Type} [CommRing B] {Y : Scheme.{0}} (π : R →+* B) (v : Spec (CommRingCat.of R) ⟶ Y)
    (s : Γ(Y, ⊤)) : valAt (Spec.map (CommRingCat.ofHom π) ≫ v) ⊤ le_top s = π (valAt v ⊤ le_top s) := by
  have h1 : ∀ {Z : Scheme.{0}} (w : Z ⟶ Y), w.appLE ⊤ ⊤ le_top = w.appTop := fun w =>
    w.appLE_eq_app
  simp only [valAt, h1]
  rw [Scheme.Hom.comp_appTop]
  have := congrArg (fun z => z.hom (v.appTop.hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom π))
  exact this

omit [IsDomain R] in
theorem pt_nsmul {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) (N : ℕ) :
    M.pt (N • e) = M.pt e ^ N := by
  induction N with
  | zero =>
    have := M.add 0 0
    rw [add_zero] at this
    simpa using (left_eq_mul.1 this)
  | succ k ih => rw [succ_nsmul, M.add, ih, pow_succ]

theorem exists_tan {T : Type} [CommGroup T] (Γ : QFGroup R T) {N : ℕ} {i : Γ.G.left ⟶ G.left}
    (h : Γ.IsTorsionAlong G x N i) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L) :
    ∃ v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left,
      v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)})
        (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  let Q := R ⧸ Ideal.span {(N : R)}
  let q : R →+* Q := Ideal.Quotient.mk _
  let c : R →+* DualNumber Q := (algebraMap Q (DualNumber Q)).comp q
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom c))
  have hc : (dualMap q).comp (algebraMap R (DualNumber R)) = c := by
    ext r <;> simp [c, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let k : Over.mk (Y.hom ≫ x) ⟶ epsAt x := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap q))) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hc])
  let k₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : q (N : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hc' : (dualMap q).comp (epsMul (N : R)) = c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    refine RingHom.ext fun r => ?_
    ext <;> simp [c, dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, -map_natCast, hN]
  have hg : (k ≫ M.pt e) ^ N = 1 := by
    rw [← MonObj.comp_pow, ← pt_nsmul, ← MonObj.comp_one k₀]
    ext1
    rw [Over.comp_left, Over.comp_left, ← Nat.cast_smul_eq_nsmul R, M.smul, ← M.tan e]
    change Spec.map _ ≫ Spec.map _ ≫ _ = Spec.map _ ≫ Spec.map _ ≫ _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc']
  obtain ⟨v, hv⟩ := (h.kernel Y (k ≫ M.pt e)).1 hg
  exact ⟨v.left, Over.w v, hv⟩

end General

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative
    (Submodule.mapQ _ _ φ.toIntLinearMap (by
      rintro _ ⟨a, rfl⟩
      exact ⟨φ a, (map_nsmul φ (p ^ n) a).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

theorem lev_surj {La : Type} [AddCommGroup La] (p n : ℕ) (t : LevGrp La p n) : ∃ a, lev p n a = t := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
  exact ⟨a, by simp [lev, ha]⟩

theorem lev_zero {La : Type} [AddCommGroup La] (p n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem finite_lev {La : Type} [AddCommGroup La] [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast pow_ne_zero n hp)⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, (natCast_zsmul a (p ^ n)).symm⟩
  infer_instance

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] {S : Scheme.{0}} {G : Over S} [GrpObj G]
  {y : Spec (CommRingCat.of O) ⟶ S} {La : Type} [AddCommGroup La] (X : TorsTower p G y La)
  {L : Type} [AddCommGroup L] [Module O L] (M : LieModel G y L)

theorem isDer_res (n : ℕ) (f : LevGrp La p (n + 1) → O) (g : LevGrp La p n → O) (w : Module.Dual O L)
    (hf : X.IsDer M (n + 1) f w) (hg : ∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) : X.IsDer M n g w := by
  obtain ⟨s, hs, hw⟩ := hf
  obtain ⟨j, hj⟩ := exists_lift (X.Γ n) (X.Γ (n + 1)) (X.tors n) (X.tors (n + 1)) (pow_dvd_pow p n.le_succ) (𝟙 G)
  rw [Over.id_left, Category.comp_id] at hj
  refine ⟨(j.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · obtain ⟨a, rfl⟩ := lev_surj p n t
    have : ((X.Γ n).pt (lev p n a)).left ≫ j.left = ((X.Γ (n + 1)).pt (lev p (n + 1) (p • a))).left := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, Over.w, Over.w]
      · rw [Category.assoc, hj, X.compat]
    rw [valAt_comp, this, hs, hg]
  · obtain ⟨v, hv1, hv2, hv3⟩ := hw e
    obtain ⟨v', h1, h2⟩ := exists_tan (X.Γ n) (X.tors n) M e
    refine ⟨v', h1, h2, ?_⟩
    have hle : Ideal.span {((p ^ (n + 1) : ℕ) : O)} ≤ Ideal.span {((p ^ n : ℕ) : O)} :=
      Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (pow_dvd_pow p n.le_succ))
    let π := Ideal.Quotient.factor hle
    have : v' ≫ j.left = Spec.map (CommRingCat.ofHom (dualMap π)) ≫ v := by
      refine left_ext _ (X.tors (n + 1)) _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, Over.w, h1, hv1, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
      · rw [Category.assoc, Category.assoc, hj, h2, hv2, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
        congr 3
        refine RingHom.ext fun r => ?_
        ext <;> simp [π, dualMap]
    have h0 : g 1 = f 1 := by simpa [lev_zero] using hg 0
    rw [valAt_comp, this, valAt_specMap, hv3, h0]
    ext <;> simp [π, dualMap]

theorem exists_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (hu : X.Induces u φ) (n : ℕ) :
    ∃ a : (X.Γ n).G ⟶ (X.Γ n).G, a.left ≫ X.i n = X.i n ≫ u.left ∧
      ∀ t, (X.Γ n).pt t ≫ a = (X.Γ n).pt (levMap p n φ t) := by
  obtain ⟨a, ha⟩ := exists_lift (X.Γ n) (X.Γ n) (X.tors n) (X.tors n) dvd_rfl u
  refine ⟨a, ha, fun t => ?_⟩
  obtain ⟨b, rfl⟩ := lev_surj p n t
  refine (X.tors n).inj _ _ _ ?_
  rw [levMap_lev, hu, Over.comp_left, Category.assoc, ha]

theorem isDer_endo (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L) (hu : X.Induces u φ)
    (hd : M.IsDiffOf u dφ) (n : ℕ) (f : LevGrp La p n → O) (w : Module.Dual O L) (hf : X.IsDer M n f w) :
    X.IsDer M n (fun t => f (levMap p n φ t)) (w ∘ₗ dφ) := by
  obtain ⟨a, ha, hpt⟩ := exists_endo X u φ hu n
  obtain ⟨s, hs, hw⟩ := hf
  refine ⟨(a.left.app ⊤).hom s, fun t => ?_, fun e => ?_⟩
  · rw [valAt_comp, ← Over.comp_left, hpt, hs]
  · obtain ⟨v, hv1, hv2, -⟩ := hw e
    obtain ⟨v', h1, h2, h3⟩ := hw (dφ e)
    refine ⟨v, hv1, hv2, ?_⟩
    have : v ≫ a.left = v' := by
      refine left_ext _ (X.tors n) _ _ ?_ ?_
      · rw [Category.assoc, Over.w, h1, hv1]
      · rw [Category.assoc, ha, h2, hd e, ← Category.assoc, hv2, Over.comp_left, Category.assoc]
    rw [valAt_comp, this, h3]
    simp only [map_one, LinearMap.comp_apply]

set_option linter.unusedVariables false in
theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) := by
  intro p hpp C _ _ _ v O _ _ _ _ _ _ S _ G _ _ _ y La _ _ _ X L _ _ M
  refine ⟨isDer_res X M, fun u _ φ dφ hu hd n f g hg => ?_⟩
  obtain rfl : g = fun t => f (levMap p n φ t) := by
    funext t
    obtain ⟨b, rfl⟩ := lev_surj p n t
    rw [hg, levMap_lev]
  refine ⟨fun hf => ?_, isDer_endo X M u φ dφ hu hd n f⟩
  obtain ⟨a, -, hpt⟩ := exists_endo X u φ hu n
  have : Finite (LevGrp La p n) := finite_lev hpp.out.ne_zero n
  exact Funct.comp_mem_btOrder O _ _ _ _ a _ hpt f hf

end PositivityTheory.HtPt.Twfunct
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFracExt.FracExt

def genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Cpt ξ :=
  ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : IsCptGen ξ)
    (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (genCpt ξ).2 = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, e]
  exact hs

theorem exists_frac {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c (genCpt M.ξ) := ⟨hc, fun _ => mem_regAt_genCpt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genCpt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem algebraMap_mem_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)
    (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ) {a : Ω}
    (ha : a ∈ chRing o x c) : algebraMap Ω Ω' a ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
  induction ha using Algebra.adjoin_induction with
  | mem a h =>
    obtain ⟨j, rfl⟩ := h
    rw [map_div₀]
    exact Algebra.subset_adjoin ⟨j, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

theorem exists_integral_div : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ]
    {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω']
    [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω',
      IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧
        v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ _ _ _ c hc a
  haveI : IsFractionRing (chRing o x c) Ω := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨u, hu, v, hv, e⟩ := exists_frac M hc z
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, e⟩
  have halg : IsAlgebraic (chRing o x c) a := by
    haveI : Algebra.IsAlgebraic (chRing o x c) Ω' :=
      (IsFractionRing.comap_isAlgebraic_iff (A := chRing o x c) (K := Ω) (C := Ω')).2 inferInstance
    exact Algebra.IsAlgebraic.isAlgebraic a
  obtain ⟨y, hy0, hi⟩ := halg.exists_integral_multiple
  have hy0' : (y : Ω) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hv : algebraMap Ω Ω' (y : Ω) ≠ 0 := (map_ne_zero _).2 hy0'
  let φ : chRing o x c →+* chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((algebraMap Ω Ω').comp (chRing o x c).val.toRingHom).codRestrict _
      fun r => algebraMap_mem_chRing x Ω' c r.2
  have hb := IsIntegral.map_of_comp_eq φ (RingHom.id Ω') (by ext r; rfl) hi
  refine ⟨y • a, algebraMap Ω Ω' (y : Ω), hb, algebraMap_mem_chRing x Ω' c y.2, hv, ?_⟩
  have e : y • a = algebraMap Ω Ω' (y : Ω) * a := by
    rw [Algebra.smul_def]; rfl
  rw [e, mul_div_cancel_left₀ _ hv]

end PositivityTheory.HtPt.Mb.LFracExt.FracExt


open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in
theorem PositivityTheory.HtPt.Mb.frac_ext : ∀ {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → ∀ a : Ω', ∃ b v : Ω', IsIntegral (chRing o (fun k => algebraMap Ω Ω' (x k)) c) b ∧ v ∈ chRing o (fun k => algebraMap Ω Ω' (x k)) c ∧ v ≠ 0 ∧ a = b / v :=
  @PositivityTheory.HtPt.Mb.LFracExt.FracExt.exists_integral_div
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {l : ℕ}

theorem pow_sy_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow2 B n) * ev ![x, z] B.sy ^ n =
      ev ![x, comp1 (B.A.act (n : O)) z] B.sy * ev ![z, x] (pow1 B n) := by
  induction n with
  | zero =>
    rw [act_zero_at, symmetric_zero_right_at B hx]
    simp only [second_power_zero, first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [second_power_succ_at B n hx hz, first_power_succ_at B n hz hx, act_succ_at B n hz, pow_succ]
    have hl := sy_law_at B hx (Z_comp1 (Z_act B.A (n : O)) hz) hz
    linear_combination (ev ![x, comp1 (B.A.act (n : O)) z, z] B.ph2 * ev ![x, z] B.sy) * ih
      + ev ![z, x] (pow1 B n) * hl

theorem first_power_zero_at {x : Pt R l d} (hx : Z x) (m : ℕ) : ev ![x, 0] (pow1 B m) = 1 := by
  induction m with
  | zero => simp only [first_power_zero, ev_one]
  | succ k ih =>
    rw [first_power_succ_at B k hx Z_zero, ih, first_form_zero_right_at B (Z_comp1 (Z_act _ _) hx) hx, one_mul]

theorem first_power_add_at {x z w : Pt R l d} (hx : Z x) (hz : Z z) (hw : Z w) (m : ℕ) :
    ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 ^ m * ev ![x, addOf B.G.F z w] (pow1 B m) := by
  induction m with
  | zero => rw [act_zero_at, second_form_zero_left_at B hz hw, first_power_zero, ev_one, ev_one, ev_one]; simp
  | succ m ih =>
    have hm : Z (comp1 (B.A.act (m : O)) x) := Z_comp1 (Z_act B.A (m : O)) hx
    rw [first_power_succ_at B m hx hz, first_power_succ_at B m hx hw, first_power_succ_at B m hx (Z_add _ hz hw), act_succ_at B m hx,
      pow_succ]
    have h1 := interchange_at B hm hx hz hw
    linear_combination (ev ![x, z] (pow1 B m) * ev ![x, w] (pow1 B m)) * h1 +
      (ev ![x, z, w] B.ph2 * ev ![comp1 (B.A.act (m : O)) x, x, addOf B.G.F z w] B.ph1) * ih

theorem pow_inter_at {x z : Pt R l d} (hx : Z x) (hz : Z z) (m n : ℕ) :
    ev ![x, z] (pow2 B n) ^ m * ev ![x, comp1 (B.A.act (n : O)) z] (pow1 B m) =
      ev ![x, z] (pow1 B m) ^ n * ev ![comp1 (B.A.act (m : O)) x, z] (pow2 B n) := by
  induction n with
  | zero => rw [act_zero_at, first_power_zero_at B hx, second_power_zero, ev_one, ev_one]; simp
  | succ n ih =>
    have hn : Z (comp1 (B.A.act (n : O)) z) := Z_comp1 (Z_act B.A (n : O)) hz
    have hm : Z (comp1 (B.A.act (m : O)) x) := Z_comp1 (Z_act B.A (m : O)) hx
    rw [second_power_succ_at B n hx hz, second_power_succ_at B n hm hz, act_succ_at B n hz, pow_succ, mul_pow]
    have h1 := first_power_add_at B hx hn hz m
    linear_combination (-ev ![x, z] (pow2 B n) ^ m) * h1 +
      (ev ![x, z] (pow1 B m) * ev ![comp1 (B.A.act (m : O)) x, comp1 (B.A.act (n : O)) z, z] B.ph2) * ih

private theorem ev_ph1_mul_ev_lam_addOf_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {X Y z : Pt R l d} (hX : Z X) (hY : Z Y) (hz : Z z) :
    ev ![X, Y, z] B₂.ph1 * ev ![addOf B₂.G.F X Y, z] lam
      = ev ![X, z] lam * ev ![Y, z] lam * ev ![comp1 φ X, comp1 φ Y, comp1 φ z] B.ph1 := by
  have hφ : Z φ := h.c₁
  have hb : ZZ ![X, Y, z] := ZZ_cons hX (ZZ_cons hY (ZZ_cons hz ZZ_nil))
  have e := congrArg (ev ![X, Y, z]) h.ph1
  simp only [FGLaw.add] at e
  simp only [ev_mul' hb] at e
  rw [ev_ev hb (ZZ_cons (Z_add B₂.G (Z_pt 0) (Z_pt 1)) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 0) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_pt 1) (ZZ_cons (Z_pt 2) ZZ_nil)),
    ev_ev hb (ZZ_cons (Z_comp1 hφ (Z_pt 0)) (ZZ_cons (Z_comp1 hφ (Z_pt 1)) (ZZ_cons (Z_comp1 hφ (Z_pt 2)) ZZ_nil)))] at e
  simp only [evV_cons, evV_nil, evalPoints_coordinatePoint hb, evalPoints_add hb _ (Z_pt _) (Z_pt _), evalPoints_comp hb _ (Z_pt _)] at e
  simpa using e

private theorem ev_zero_lam_eq_one_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {z : Pt R l d} (hz : Z z) : ev ![0, z] lam = 1 := by
  have hb : ZZ ![z] := ZZ_cons hz ZZ_nil
  have e := congrArg (ev ![z]) h.ax.1
  rw [ev_ev hb (ZZ_cons Z_zero (ZZ_cons (Z_pt 0) ZZ_nil)), ev_one] at e
  simpa [evV_cons, evV_nil, evalPoints_zero, evalPoints_coordinatePoint hb] using e

theorem iso_first_power_at {B} {B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam)
    {x z : Pt R l d} (hx : Z x) (hz : Z z) (n : ℕ) :
    ev ![x, z] (pow1 B₂ n) * ev ![comp1 (B₂.A.act (n : O)) x, z] lam =
      ev ![x, z] lam ^ n * ev ![comp1 φ x, comp1 φ z] (pow1 B n) := by
  have hφ : Z φ := h.c₁
  induction n with
  | zero =>
    rw [act_zero_at, ev_zero_lam_eq_one_of_isIso h hz]
    simp only [first_power_zero, ev_one, pow_zero, mul_one]
  | succ n ih =>
    rw [first_power_succ_at B₂ n hx hz, act_succ_at B₂ n hx, first_power_succ_at B n (Z_comp1 hφ hx) (Z_comp1 hφ hz), pow_succ]
    have hP := ev_ph1_mul_ev_lam_addOf_of_isIso h (Z_comp1 (Z_act B₂.A (n : O)) hx) hx hz
    have hc : comp1 φ (comp1 (B₂.A.act (n : O)) x) = comp1 (B.A.act (n : O)) (comp1 φ x) := by
      rw [← germComp1_germComp1_eq_substitute φ (Z_act B₂.A _) hx, h.act, germComp1_germComp1_eq_substitute _ hφ hx]
    rw [hc] at hP
    linear_combination ev ![x, z] (pow1 B₂ n) * hP
      + (ev ![x, z] lam * ev ![comp1 (B.A.act (n : O)) (comp1 φ x), comp1 φ x, comp1 φ z] B.ph1) * ih

theorem pow_sy : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  intro R _ d O _ _ B n
  have e := pow_sy_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

theorem pow_inter : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  intro R _ d O _ _ B m n
  have e := pow_inter_at B (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) m n
  simp only [eval_identity_two] at e
  exact e

theorem iso_first_power : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  intro R _ d O _ _ B B₂ φ ψ lam n h
  have e := iso_first_power_at h (Z_pt (R := R) (d := d) (0 : Fin 2)) (Z_pt 1) n
  simp only [eval_identity_two] at e
  exact e

end PositivityTheory.HtPt.Cc
end
end
