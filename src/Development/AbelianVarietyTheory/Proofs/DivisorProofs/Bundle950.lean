module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle862
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle698
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle898
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMat

private theorem topS_tensor_left_ext {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) {Z : Scheme.{0}}
    (f g : Z ⟶ (topS Rg ⊗ A).left) (h : f ≫ (snd (topS Rg) A).left = g ≫ (snd (topS Rg) A).left) : f = g := by
  have P := IsPullback.of_hasPullback (topS Rg).hom A.hom
  have h' : f ≫ pullback.snd (topS Rg).hom A.hom = g ≫ pullback.snd (topS Rg).hom A.hom := h
  apply P.hom_ext
  · have hm : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    rw [← cancel_mono (topS Rg).hom, Category.assoc, Category.assoc, P.w, ← Category.assoc, h', Category.assoc]
  · exact h'

end GlobalTheory.HomFixMat

namespace GlobalTheory.HomFixMat

theorem mat_determines : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A₁ B₁ : Over (Sp R)) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁) (A₂ B₂ : Over (Sp R)) [GrpObj A₂] [GrpObj B₂] (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → IsTest A B L M t A₂ B₂ φA₂ φB₂ Φ₂ → IsMat L M k bA bB eA eB t A₁ B₁ φA₁ φB₁ Φ₁ c → IsMat L M k bA bB eA eB t A₂ B₂ φA₂ φB₂ Φ₂ c → IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ (𝟙 (Sp R)) := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A₁ B₁ _ _ φA₁ φB₁ Φ₁ A₂ B₂ _ _ φA₂ φB₂ Φ₂ c T₁ T₂ M₁ M₂
  obtain ⟨-, hBab, hL, hM, -, -, -, -, hva, -, hbc⟩ := hH
  let ψA : A₂.left ⟶ A₁.left := T₁.1.1.lift φA₂ A₂.hom T₂.1.1.w
  let ψB : B₂.left ⟶ B₁.left := T₁.2.1.1.lift φB₂ B₂.hom T₂.2.1.1.w
  have hψA1 : ψA ≫ φA₁ = φA₂ := T₁.1.1.lift_fst _ _ _
  have hψA2 : ψA ≫ A₁.hom = A₂.hom := T₁.1.1.lift_snd _ _ _
  have hψB1 : ψB ≫ φB₁ = φB₂ := T₁.2.1.1.lift_fst _ _ _
  have hψB2 : ψB ≫ B₁.hom = B₂.hom := T₁.2.1.1.lift_snd _ _ _
  have gA : IsGrpPullback A₂ A₁ (𝟙 _) ψA :=
    IsGrpPullback.cancel T₁.1 (by rw [Category.id_comp, hψA1]; exact T₂.1) (by rw [hψA2, Category.comp_id])
  have gB : IsGrpPullback B₂ B₁ (𝟙 _) ψB :=
    IsGrpPullback.cancel T₁.2.1 (by rw [Category.id_comp, hψB1]; exact T₂.2.1) (by rw [hψB2, Category.comp_id])
  refine ⟨ψA, ψB, gA, gB, hψA1, hψB1, ?_⟩
  suffices key : Φ₂.left ≫ φB₂ = ψA ≫ Φ₁.left ≫ φB₁ by
    apply T₁.2.1.1.hom_ext
    · rw [Category.assoc, hψB1, key, Category.assoc]
    · rw [Category.assoc, hψB2, Over.w Φ₂, Category.assoc, Over.w Φ₁, hψA2]

  obtain ⟨ψA₁, ψB₁, eA₁, eB₁, g₁⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₁
  obtain ⟨ψA₂, ψB₂, eA₂, eB₂, g₂⟩ := GlobalTheory.T.isMatrixIdentity_germ_pullback_chart M₂
  obtain ⟨x, b', hx, hb', hemb⟩ := GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis B M k bB hBab hM hva hbc
  have hG : ψA ≫ ψA₁ = ψA₂ := topS_tensor_left_ext A _ _ (by rw [Category.assoc, eA₁, eA₂, hψA1])
  let H : (baseAt x ⊗ B).left ⟶ (topS Rg ⊗ B).left := (homAt x ▷ B).left
  have hHi : IsIso (homAt x) := by
    have : IsIso ((Over.forget _).map (homAt x)) := hx
    exact isIso_of_reflects_iso (homAt x) (Over.forget _)
  have hH : IsIso H := (inferInstance : IsIso ((Over.forget _).map (homAt x ▷ B)))
  have hHs : H ≫ (snd (topS Rg) B).left = (snd (baseAt x) B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  let F₁ : A₂.left ⟶ (topS Rg ⊗ B).left := ψA ≫ Φ₁.left ≫ ψB₁
  let F₂ : A₂.left ⟶ (topS Rg ⊗ B).left := Φ₂.left ≫ ψB₂
  suffices hF : F₂ ≫ inv H = F₁ ≫ inv H by
    have e1 : F₂ = F₁ := by simpa using congrArg (· ≫ H) hF
    have e2 : F₂ ≫ (snd (topS Rg) B).left = F₁ ≫ (snd (topS Rg) B).left := by rw [e1]
    simp only [F₁, F₂, Category.assoc] at e2
    rwa [eB₁, eB₂] at e2

  have memw : ∀ {P Q : Scheme.{0}} (W : LB Q) (φ : P ⟶ Q) (j : Fin 1 → W.ι) (y : P), φ y ∈ W.U (j 0) →
      y ∈ LB.wchart W (fun _ : Fin 1 => φ) j := fun W φ j y h =>
    Set.mem_iInter.2 fun i => by rw [Subsingleton.elim i 0]; exact h
  have hsx : (snd (topS Rg) B).left = inv H ≫ (snd (baseAt x) B).left := by
    rw [← hHs, IsIso.inv_hom_id_assoc]
  have hbase : ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseAt x ⊗ B).left) (z : Z) (pM : Fin 1 → M.ι) (j : Fin mB),
      r z ∈ (LPow B M (k : ℤ) (baseAt x)).U pM →
      gs r z _ ((b' j).f pM) = gs (r ≫ H) z _ ((bB j).f pM) := by
    intro Z r z pM j hz
    rw [hb' j pM, gs_res _ _ _ hz, gs_pull]
    exact chart_le_res B M (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (k : ℤ) pM hz
  have hmono : Mono (baseAt x).hom := by
    have : Mono (topS Rg).hom := by
      change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
    change Mono (x ≫ (topS Rg).hom); infer_instance
  have hπ : ∀ F : A₂.left ⟶ (topS Rg ⊗ B).left, F ≫ inv H ≫ (fst (baseAt x) B).left ≫ (baseAt x).hom =
      F ≫ (snd (topS Rg) B).left ≫ B.hom := by
    intro F
    have w : (fst (baseAt x) B).left ≫ (baseAt x).hom = (snd (baseAt x) B).left ≫ B.hom :=
      pullback.condition
    rw [w, hsx]; simp only [Category.assoc]
  refine GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively (fst (baseAt x) B).left b' hemb _ _ ?_ ?_
  · rw [← cancel_mono (baseAt x).hom]
    simp only [Category.assoc]
    rw [hπ, hπ]
    simp only [F₁, F₂, Category.assoc]
    rw [reassoc_of% eB₁, reassoc_of% eB₂, T₁.2.1.1.w, T₂.2.1.1.w, reassoc_of% (Over.w Φ₂), reassoc_of% (Over.w Φ₁),
      reassoc_of% hψA2]
  · intro z
    obtain ⟨q0, hq0⟩ := exists_chart hL (φA₂ z)
    obtain ⟨p₁, hp₁⟩ := exists_chart hM ((ψA ≫ Φ₁.left ≫ φB₁) z)
    obtain ⟨p₂, hp₂⟩ := exists_chart hM ((Φ₂.left ≫ φB₂) z)
    have mA₂ : (𝟙 A₂.left ≫ ψA₂) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      refine memw L _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, eA₂]; exact hq0
    have mA₁ : (ψA ≫ ψA₁) z ∈ (LPow A L (k : ℤ) (topS Rg)).U (fun _ => q0) := by
      rw [hG]; simpa using mA₂
    have mB₂ : (𝟙 A₂.left ≫ Φ₂.left ≫ ψB₂) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₂) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.id_comp, Category.assoc, eB₂]; exact hp₂
    have mB₁ : (ψA ≫ Φ₁.left ≫ ψB₁) z ∈ (LPow B M (k : ℤ) (topS Rg)).U (fun _ => p₁) := by
      refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, eB₁]; exact hp₁
    obtain ⟨u₂, hu₂⟩ := g₂ A₂.left (𝟙 _) z _ _ mB₂ mA₂
    obtain ⟨u₁, hu₁⟩ := g₁ A₂.left ψA z _ _ mB₁ mA₁
    simp only [Category.id_comp] at hu₂
    rw [hψA2, hG] at hu₁
    refine ⟨fun j => ∑ i, gs A₂.hom z ⊤ (c i j) * gs ψA₂ z _ ((bA i).f (fun _ => q0)), ⟨fun _ => p₂, ?_, u₂, fun l => ?_⟩,
      ⟨fun _ => p₁, ?_, u₁, fun l => ?_⟩⟩
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₂, Category.assoc]; rw [eB₂]; exact hp₂)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₂ l
    · refine memw M _ _ _ ?_
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁
    · rw [hbase _ _ _ _ _ (memw M _ _ _ (by rw [← Scheme.Hom.comp_apply, Category.assoc, ← hsx]; simp only [F₁, Category.assoc]; rw [eB₁]; exact hp₁)),
        Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact hu₁ l

end GlobalTheory.HomFixMat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixOpen

variable {A₀ X T : Scheme.{0}} {N : LB A₀} {mA mB : ℕ}

theorem isUnit_comb_chart (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (z : X) {q q' : N.ι} (hq : φ z ∈ N.U q) (hq' : φ z ∈ N.U q') (j : Fin mB) :
    IsUnit (comb a φ p c z q j) ↔ IsUnit (comb a φ p c z q' j) := by
  have e : comb a φ p c z q j = (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    simp only [comb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_compat (a i) φ z hq hq', mul_left_comm]
  rw [e, Units.isUnit_units_mul]

theorem comb_comp {Y : Scheme.{0}} (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (h : Y ⟶ X) (y : Y) (q : N.ι) (hq : φ (h y) ∈ N.U q) (j : Fin mB) :
    comb a (h ≫ φ) (h ≫ p) c y q j = (h.stalkMap y).hom (comb a φ p c (h y) q j) := by

  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp h p y ⊤ trivial, gs_comp h φ y (N.U q) hq]

theorem gs_top {Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (z : X) (c : Γ(Z, ⊤)) :
    gs f z ⊤ (g.appTop.hom c) = gs (f ≫ g) z ⊤ c :=
  gs_pull f g z ⊤ trivial c

theorem gs_sum' {Y : Scheme.{0}} (f : X ⟶ Y) (z : X) (U : Y.Opens) (h : f z ∈ U) {n : ℕ} (b : Fin n → Γ(Y, U)) :
    gs f z U (∑ i, b i) = ∑ i, gs f z U (b i) := by

  simp only [gs_eq f z U h, map_sum]

def good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Set X :=
  {z | ∃ q, φ z ∈ N.U q ∧ ∃ j, IsUnit (comb a φ p c z q j)}

def combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) : Γ(X, φ ⁻¹ᵁ N.U q) :=
  ∑ i, (X.presheaf.map (homOfLE le_top).op).hom (p.appTop.hom (c i j)) * (φ.app (N.U q)).hom ((a i).f q)

theorem gs_combFn (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (q : N.ι)
    (j : Fin mB) (z : X) (hz : φ z ∈ N.U q) : gs (𝟙 X) z _ (combFn a φ p c q j) = comb a φ p c z q j := by
  have hz' : (𝟙 X) z ∈ φ ⁻¹ᵁ N.U q := hz
  rw [combFn, gs_sum' (𝟙 X) z _ hz']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul _ z _ hz', gs_res _ z le_top hz', gs_top, gs_pull (𝟙 X) φ z (N.U q) hz, Category.id_comp,
    Category.id_comp]

theorem isOpen_good (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) :
    IsOpen (good a φ p c) := by
  have e : good a φ p c = ⋃ q, ⋃ j, (X.basicOpen (combFn a φ p c q j) : Set X) := by
    ext z
    simp only [good, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨q, hq, j, hu⟩
      refine ⟨q, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq] at hu
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).1 hu
    · rintro ⟨q, j, hz⟩
      have hq : φ z ∈ N.U q := X.basicOpen_le _ hz
      refine ⟨q, hq, j, ?_⟩
      rw [← gs_combFn a φ p c q j z hq]
      exact (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) z _ hq _).2 hz
  rw [e]
  exact isOpen_iUnion fun q => isOpen_iUnion fun j => (X.basicOpen _).isOpen

end GlobalTheory.HomFixOpen

namespace GlobalTheory.HomFixOpen

theorem main : ∀ (Rg : Type) [CommRing Rg] (A₀ : Scheme.{0}) (f : A₀ ⟶ Sp Rg) [UniversallyClosed f] (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N), N.IsLB → ∃ U : (Sp (MvPolynomial (Fin (mA * mB)) Rg)).Opens, ∀ (T X' : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X' ⟶ A₀) (p : X' ⟶ T), IsPullback φ p f (g ≫ affπ Rg (mA * mB)) → (GlobalTheory.HomFixUniv.Generates a φ p (matOf g) ↔ ∀ τ, g τ ∈ U) := by
  intro Rg _ A₀ f _ N mA mB a hN
  let π₁ := pullback.fst f (affπ Rg (mA * mB))
  let π₂ := pullback.snd f (affπ Rg (mA * mB))
  let G := good a π₁ π₂ (matOf (𝟙 (Sp (MvPolynomial (Fin (mA * mB)) Rg))))
  have hG : IsOpen G := isOpen_good _ _ _ _
  have hC : IsClosed (π₂ '' Gᶜ) := π₂.isClosedMap _ hG.isClosed_compl
  refine ⟨⟨(π₂ '' Gᶜ)ᶜ, hC.isOpen_compl⟩, fun T X' g φ p hP => ?_⟩
  have w : φ ≫ f = (p ≫ g) ≫ affπ Rg (mA * mB) := by rw [Category.assoc]; exact hP.w
  let h := pullback.lift φ (p ≫ g) w
  have h1 : h ≫ π₁ = φ := pullback.lift_fst _ _ _
  have h2 : h ≫ π₂ = p ≫ g := pullback.lift_snd _ _ _
  have hπ₁ : ∀ z, π₁ (h z) = φ z := fun z => by rw [← Scheme.Hom.comp_apply, h1]
  have key : ∀ z q j, φ z ∈ N.U q → comb a φ p (matOf g) z q j =
      (h.stalkMap z).hom (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j) := by
    intro z q j hq
    rw [← comb_comp a π₁ π₂ _ h z q (by rw [hπ₁]; exact hq) j]
    simp only [comb, h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [h2, matOf, matOf, coord, coord, gs_top, gs_top, Category.comp_id]
  have unitIff : ∀ z q j, φ z ∈ N.U q → (IsUnit (comb a φ p (matOf g) z q j) ↔
      IsUnit (comb a π₁ π₂ (matOf (𝟙 _)) (h z) q j)) := by
    intro z q j hq; rw [key z q j hq]; exact isUnit_map_iff _ _
  have stepA : Generates a φ p (matOf g) ↔ ∀ z, h z ∈ G := by
    constructor
    · intro hg z
      obtain ⟨q, hq⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hN (φ z)
      obtain ⟨j, hj⟩ := hg z q hq
      exact ⟨q, by rw [hπ₁]; exact hq, j, (unitIff z q j hq).1 hj⟩
    · intro hg z q hq
      obtain ⟨q', hq', j, hj⟩ := hg z
      exact ⟨j, (unitIff z q j hq).2 ((isUnit_comb_chart a π₁ π₂ _ (h z) hq' (by rw [hπ₁]; exact hq) j).1 hj)⟩
  rw [stepA]
  have hP' : IsPullback h p π₂ g := IsPullback.of_right (by rw [h1]; exact hP) h2 (IsPullback.of_hasPullback _ _)
  constructor
  · intro hg τ
    show g τ ∈ (π₂ '' Gᶜ)ᶜ
    rintro ⟨w', hw, he⟩
    obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π₂) (g := g) w' τ he
    apply hw
    have e : h (hP'.isoPullback.inv y) = w' := by
      rw [← Scheme.Hom.comp_apply, hP'.isoPullback_inv_fst, hy1]
    rw [← e]; exact hg _
  · intro hg z
    by_contra hz
    exact hg (p z) ⟨h z, hz, by rw [← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply]⟩

end GlobalTheory.HomFixOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem topS_hom_ext {Rg : Type} [CommRing Rg] {Y : Over (Sp Rg)} (u v : Y ⟶ topS Rg) : u = v := by
  have hm : Mono (topS Rg).hom := by
    change Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w u, Over.w v]

instance isIso_snd_left {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) :
    IsIso (snd (topS Rg) A).left := by
  have : IsIso (snd (topS Rg) A) := by
    refine ⟨⟨lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A), ?_, ?_⟩⟩
    · refine CartesianMonoidalCategory.hom_ext _ _ (topS_hom_ext _ _) ?_
      simp
    · simp
  exact (Over.forget _).map_isIso (snd (topS Rg) A)

theorem fA_flat_isProjBy_universallyClosed : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → RelAmple A L → Flat (GlobalTheory.HomFixUniv.fA A) ∧ GlobalTheory.AbLaw.IsProjBy (GlobalTheory.HomFixUniv.fA A) ∧ UniversallyClosed (GlobalTheory.HomFixUniv.fA A) := by
  intro Rg _ A _ L hA hL hamp
  have hsq : IsPullback (snd (topS Rg) A).left (fA A) A.hom (𝟙 (Sp Rg)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w (snd (topS Rg) A)⟩
  obtain ⟨hproj, hsm, hpr, -⟩ :=
    GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral (Sp Rg) A L hA hL hamp Rg (𝟙 _) _ _ (fA A) hsq
  exact ⟨inferInstance, hproj, inferInstance⟩

end GlobalTheory.HomFixUniv
end
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem yF_apply_sum (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    yF X w τ a b = ∑ k, nmat X w τ a k * gsB X w τ k b := by
  simp [yF, yM, Matrix.mul_apply, mat]

theorem gsB_differentiableAt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w => gsB X w τ a b) 0 := by
  obtain ⟨R, hR, hball⟩ := exists_ball X hx
  have hs : {w | cpt X x w ∈ X.dom} ∈ nhds (0 : V (nd X)) :=
    Filter.mem_of_superset (Metric.ball_mem_nhds 0 hR) (fun w hw => hball w hw)
  exact ((GlobalTheory.T.contDiffOn_gramSchmidtUpperTriangularFactor X hx τ a b).contDiffAt hs).differentiableAt (by simp)

theorem nmat_differentiableAt (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ a b) 0 :=
  ((PoinPf.diff_nmat X τ a b).restrictScalars ℝ) 0

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    nmat X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  have h := congrFun (congrFun (PoinPf.nmat_zero X τ) a) b
  simpa [mat] using h

theorem gsB_zero_apply (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    gsB X 0 τ a b = (1 : Matrix (Fin r) (Fin r) ℂ) a b := by
  rw [gsB_zero]

theorem dY_lower (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ)
    (a b : Fin r) (hba : b < a) : dY X z τ a b = nmat X z τ a b := by
  have hS := (GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt X hx).hasFDerivAt
  have h1 := hasFDerivAt_pi'.1 hS τ
  have h2 := hasFDerivAt_pi'.1 h1 a
  have h3 := hasFDerivAt_pi'.1 h2 b
  have hT : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) 0 :=
    HasFDerivAt.fun_sum (fun k _ =>
      (nmat_differentiableAt X τ a k).hasFDerivAt.mul (gsB_differentiableAt X hx τ k b).hasFDerivAt)
  have h3' : HasFDerivAt (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b)
      ((ContinuousLinearMap.proj b).comp ((ContinuousLinearMap.proj a).comp
        ((ContinuousLinearMap.proj τ).comp (dY X)))) 0 := by
    have : (fun w => ∑ k, nmat X w τ a k * gsB X w τ k b) = fun w => yF X w τ a b := by
      funext w; rw [yF_apply_sum]
    rw [this]; exact h3
  have hU := congrArg (fun L => L z) (h3'.unique hT)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at hU
  rw [hU]
  have hB0 : (fun w : V (nd X) => gsB X w τ a b) = fun _ => 0 := by
    funext w; exact gsB_lower X w τ hba
  set e := (Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), hba⟩⟩
  have hN : (fun w : V (nd X) => nmat X w τ a b) =
      ⇑((EuclideanSpace.proj e : V (nd X) →L[ℂ] ℂ).restrictScalars ℝ) := by
    funext w; simp [nmat, hba, e]; rfl
  have hsum : (∑ k, (nmat X 0 τ a k • fderiv ℝ (fun w => gsB X w τ k b) 0 +
        gsB X 0 τ k b • fderiv ℝ (fun w => nmat X w τ a k) 0)) =
      fderiv ℝ (fun w => gsB X w τ a b) 0 + fderiv ℝ (fun w => nmat X w τ a b) 0 := by
    simp only [nmat_zero_apply, gsB_zero_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hsum, ContinuousLinearMap.add_apply]
  rw [hB0, hN, fderiv_const_apply, ContinuousLinearMap.fderiv, ContinuousLinearMap.zero_apply, zero_add]
  simp [nmat, hba, e] <;> rfl

end GlobalTheory.SUChartSection
end

section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

theorem _root_.GlobalTheory.T.genericRowSubstitution_coeff_exponent_le_degree : ∀ (O : Type) [CommRing O] (N : ℕ) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → ∀ m, (GlobalTheory.HighWt.genSub O N f).coeff m ≠ 0 → ∀ v, m v ≤ D := by
  first | exact @GlobalTheory.GenSubDeg.genSub_coeff_le | exact GlobalTheory.GenSubDeg.genSub_coeff_le | (intros; apply GlobalTheory.GenSubDeg.genSub_coeff_le <;> assumption)
end

section

open NumberField GlobalTheory.ExpFrame

theorem _root_.GlobalTheory.T.integralCrystallineBlockData_of_reductionPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  first | exact @GlobalTheory.WachBlock.integralBlock_of_blockPair | exact GlobalTheory.WachBlock.integralBlock_of_blockPair | (intros; apply GlobalTheory.WachBlock.integralBlock_of_blockPair <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.pure_endomorphism_hom_lift_square_zero : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  first | exact @GlobalTheory.pureLift_step | exact GlobalTheory.pureLift_step | (intros; apply GlobalTheory.pureLift_step <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.appellHumbertFactor_imForm_integral_on_lattice : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  first | exact @GlobalTheory.TorusRM.ahFactor_im_int | exact GlobalTheory.TorusRM.ahFactor_im_int | (intros; apply GlobalTheory.TorusRM.ahFactor_im_int <;> assumption)
end
end

section

open NumberField


theorem _root_.GlobalTheory.T.idealExtend_conj_mul_eq_absNorm : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)), (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E, D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧ (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  first | exact @GlobalTheory.VacRead.conj_mul_cE_absNorm | exact GlobalTheory.VacRead.conj_mul_cE_absNorm | (intros; apply GlobalTheory.VacRead.conj_mul_cE_absNorm <;> assumption)
end
