module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appLE_univ_congr_of_eq {V Z : Scheme.{0}} {f g : V ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ g ⁻¹ᵁ U) : f.appLE U ⊤ e = g.appLE U ⊤ e' := by
  subst hfg; rfl

private lemma appLE_lift_eq {Y V : Scheme.{0}} (C : Y.Opens) (l : V ⟶ (C : Scheme.{0}))
    (h : ⊤ ≤ (l ≫ C.ι) ⁻¹ᵁ C) : (l ≫ C.ι).appLE C ⊤ h = C.topIso.inv ≫ l.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE l C.ι C ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  simp
  congr 1

private lemma eq_of_appLE_eq {Y V : Scheme.{0}} (C : Y.Opens) (hC : IsAffineOpen C) (y y' : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (h' : ⊤ ≤ y' ⁻¹ᵁ C) (e : y.appLE C ⊤ h = y'.appLE C ⊤ h') : y = y' := by
  have r : ∀ z : V ⟶ Y, ⊤ ≤ z ⁻¹ᵁ C → Set.range z ⊆ Set.range C.ι := by
    rintro z hz _ ⟨x, rfl⟩
    simpa using hz (Set.mem_univ x)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ C.ι = y := ⟨_, IsOpenImmersion.lift_fac C.ι y (r y h)⟩
  obtain ⟨l', rfl⟩ : ∃ l, l ≫ C.ι = y' := ⟨_, IsOpenImmersion.lift_fac C.ι y' (r y' h')⟩
  haveI : IsAffine (C : Scheme.{0}) := hC
  rw [appLE_lift_eq, appLE_lift_eq] at e
  have e2 : l.appTop = l'.appTop := (cancel_epi C.topIso.inv).mp e
  rw [ext_of_isAffine e2]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), y ≫ π = y' ≫ π → uV B α k y h = uV B α k y' h' → y = y' := by
  intro K _ W Z Y q i π D d B α k V y y' h h' hπ hu
  have hle := (B.c α).C_le k
  refine eq_of_appLE_eq _ ((B.c α).C_aff k) y y' h h' ?_
  have hpi : ∀ r : Γ(Z, B.V α), (y.appLE _ ⊤ h).hom ((π.appLE (B.V α) _ hle).hom r) =
      (y'.appLE _ ⊤ h').hom ((π.appLE (B.V α) _ hle).hom r) := by
    intro r
    have e1 := Scheme.Hom.appLE_comp_appLE y π (B.V α) ((B.c α).C k) ⊤ hle h
    have e2 := Scheme.Hom.appLE_comp_appLE y' π (B.V α) ((B.c α).C k) ⊤ hle h'
    have e3 := e1.trans ((appLE_univ_congr_of_eq hπ (B.V α) _ _).trans e2.symm)
    exact congrArg (fun t => t.hom r) e3
  have hP := MvPolynomial.ringHom_ext
    (f := (y.appLE _ ⊤ h).hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (g := (y'.appLE _ ⊤ h').hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (fun r => by simpa using hpi r)
    (fun m => by simpa [uV] using congrFun hu m)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  obtain ⟨P, rfl⟩ := (B.c α).surj k s
  exact congrArg (fun t => t P) hP
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma restr_sec {V Z : Scheme.{0}} (f : V ⟶ Z) {U U₂ : V.Opens} {N N₂ : Z.Opens}
    (hN : N₂ ≤ N) (hUU : U₂ ≤ U) (hU : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ N) (hU₂ : ⊤ ≤ (U₂.ι ≫ f) ⁻¹ᵁ N₂)
    (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (h : U.ι.appTop.hom s = ((U.ι ≫ f).appLE N ⊤ hU).hom g) :
    U₂.ι.appTop.hom s =
      ((U₂.ι ≫ f).appLE N₂ ⊤ hU₂).hom ((Z.presheaf.map (homOfLE hN).op).hom g) := by
  have e1 : U₂.ι.appTop = U.ι.appTop ≫ (V.homOfLE hUU).appTop := by
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
  have hT : (⊤ : (U₂ : Scheme.{0}).Opens) ≤ (V.homOfLE hUU) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e0 : (V.homOfLE hUU).appLE ⊤ ⊤ hT = (V.homOfLE hUU).appTop :=
    (Scheme.Hom.app_eq_appLE (V.homOfLE hUU)).symm
  have e2 : Z.presheaf.map (homOfLE hN).op ≫ (U₂.ι ≫ f).appLE N₂ ⊤ hU₂ =
      (U.ι ≫ f).appLE N ⊤ hU ≫ (V.homOfLE hUU).appTop := by
    rw [← e0, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [← Category.assoc, Scheme.homOfLE_ι]
  have e3 := congrArg (fun φ => φ.hom g) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  rw [e1, CommRingCat.hom_comp, RingHom.comp_apply, h, ← e3]

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
  {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ}

private lemma tN_res (B : Blow q i π D d) (α : B.ι) {N N₂ : Z.Opens} (h : N ≤ B.V α)
    (hN : N₂ ≤ N) (m : Fin d) :
    tN B α (hN.trans h) m = (Z.presheaf.map (homOfLE hN).op).hom (tN B α h m) := by
  simp only [tN]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma isTr_res (B : Blow q i π D d) (α β : B.ι) {N N₂ : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (hN : N₂ ≤ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hN.trans h₁) (hN.trans h₂) (G.map (Z.presheaf.map (homOfLE hN).op).hom) := by
  intro m

  rw [tN_res B β h₂ hN, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, tN_res B α h₁ hN]
  rfl

private lemma isTr_comp (B : Blow q i π D d) (α β γ : B.ι) {N : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (h₃ : N ≤ B.V γ) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) (hG' : IsTr B β γ h₂ h₃ G') :
    IsTr B α γ h₁ h₃ (G' * G) := by
  intro m
  rw [hG' m]
  simp only [hG _, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β γ : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B β γ p M' → LocMat B α γ p (M' * M) := by
  intro K _ W Z Y q i π D d B α β γ V p M M' h h' x
  obtain ⟨U, N, hx, hNa, h₁, h₂, hU, G, hG, hM⟩ := h x
  obtain ⟨U', N', hx', hNa', h₁', h₂', hU', G', hG', hM'⟩ := h' x
  have hxN : (p ≫ i) x ∈ N := hU (Set.mem_univ (⟨x, hx⟩ : (U : Scheme.{0})))
  have hxN' : (p ≫ i) x ∈ N' := hU' (Set.mem_univ (⟨x, hx'⟩ : (U' : Scheme.{0})))
  obtain ⟨N₂, hA, hxN₂, hle⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') ⟨hxN, hxN'⟩
  have hl₁ : N₂ ≤ N := fun y hy => (hle hy).1
  have hl₂ : N₂ ≤ N' := fun y hy => (hle hy).2
  let U₂ : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N₂
  have hUl : U₂ ≤ U := fun y hy => hy.1.1
  have hUl' : U₂ ≤ U' := fun y hy => hy.1.2
  have hU₂ : ⊤ ≤ (U₂.ι ≫ p ≫ i) ⁻¹ᵁ N₂ := by
    intro y _
    exact y.2.2
  refine ⟨U₂, N₂, ⟨⟨hx, hx'⟩, hxN₂⟩, hA, hl₁.trans h₁, hl₂.trans h₂', hU₂,
    G'.map (Z.presheaf.map (homOfLE hl₂).op).hom * G.map (Z.presheaf.map (homOfLE hl₁).op).hom,
    ?_, ?_⟩
  · exact isTr_comp B α β γ _ (hl₁.trans h₂) _ _ _ (isTr_res B α β h₁ h₂ hl₁ G hG)
      (isTr_res B β γ h₁' h₂' hl₂ G' hG')
  · rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · ext a b
      exact restr_sec (p ≫ i) hl₂ hUl' hU' hU₂ _ _ (congrFun (congrFun hM' a) b)
    · ext a b
      exact restr_sec (p ≫ i) hl₁ hUl hU hU₂ _ _ (congrFun (congrFun hM a) b)
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem blowup_chart_relation (B : Blow q i π D d) (α : B.ι) (k n : Fin d) :
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t n) =
      (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) * (B.c α).u k n := by
  have hmem : (MvPolynomial.C ((B.c α).t n) - MvPolynomial.C ((B.c α).t k) * MvPolynomial.X n :
      MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨n, rfl⟩)
  have h0 := RingHom.mem_ker.mp hmem
  rw [map_sub, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_C] at h0
  exact sub_eq_zero.mp h0

private theorem res_chain {V : Scheme.{0}} (y : V ⟶ Y) {A N : Z.Opens} {C : Y.Opens} (hC : C ≤ π ⁻¹ᵁ A)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (n : N ≤ A) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (s : Γ(Z, A)) :
    (y.appLE C ⊤ h).hom ((π.appLE A C hC).hom s) =
      ((y ≫ π).appLE N ⊤ hy).hom ((Z.presheaf.map (homOfLE n).op).hom s) := by
  have e1 := Scheme.Hom.appLE_comp_appLE y π A C ⊤ hC h
  have e2 := Scheme.Hom.map_appLE (y ≫ π) hy (homOfLE n).op
  have : π.appLE A C hC ≫ y.appLE C ⊤ h = Z.presheaf.map (homOfLE n).op ≫ (y ≫ π).appLE N ⊤ hy := by
    rw [e1, e2]
  exact congrArg (fun φ => φ.hom s) this

private theorem top_inv {V : Scheme.{0}} {C : Y.Opens} (g : V ⟶ (C : Scheme.{0})) (h : ⊤ ≤ (g ≫ C.ι) ⁻¹ᵁ C) (s : Γ(Y, C)) :
    g.appTop.hom (C.topIso.inv.hom s) = ((g ≫ C.ι).appLE C ⊤ h).hom s := by
  have e0 : (⊤ : (C : Scheme.{0}).Opens) ≤ C.ι ⁻¹ᵁ C := fun x _ => x.2
  have e1 := Scheme.Hom.appLE_comp_appLE g C.ι C ⊤ ⊤ e0 (fun x _ => trivial)
  have e2 : C.ι.appLE C ⊤ e0 = C.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    refine (Y.presheaf.map_comp _ _).symm.trans ?_
    exact congrArg _ (Subsingleton.elim _ _)
  have e3 : g.appLE ⊤ ⊤ (fun x _ => trivial) = g.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (g.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [e2, e3] at e1
  exact congrArg (fun φ => φ.hom s) e1

private theorem f_sec (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) :
    B.f (secOf B α k y h) =
      (y.appLE ((B.c α).C k) ⊤ h).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) := by
  unfold secOf
  rw [B.f_nat, B.f_σ]
  have hg : IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h) ≫ ((B.c α).C k).ι = y :=
    IsOpenImmersion.lift_fac _ _ _
  have := top_inv (IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h)) (by rw [hg]; exact h)
    ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k))
  rw [this]
  simp only [hg]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvNzd :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (y : V ⟶ Y) (α β : B.ι) (k l : Fin d) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l) {N : Z.Opens} (n₁ : N ≤ B.V α) (n₂ : N ≤ B.V β) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β n₁ n₂ G → (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) ∈ nonZeroDivisors Γ(V, ⊤) → (G.map ((y ≫ π).appLE N ⊤ hy).hom).mulVec (uV B α k y h₁) = (((D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm))⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • uV B β l y h₂ := by
  intro K _ W Z Y q i π D d B V y α β k l h₁ h₂ N n₁ n₂ hy G hG hnz
  set a := ((y ≫ π).appLE N ⊤ hy).hom with ha
  set Tk := (y.appLE ((B.c α).C k) ⊤ h₁).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) with hTk
  set Tl := (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) with hTl
  set u := D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm) with hu
  have hα : ∀ n, a (tN B α n₁ n) = Tk * uV B α k y h₁ n := by
    intro n
    have := res_chain y ((B.c α).C_le k) h₁ n₁ hy ((B.c α).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hβ : ∀ n, a (tN B β n₂ n) = Tl * uV B β l y h₂ n := by
    intro n
    have := res_chain y ((B.c β).C_le l) h₂ n₂ hy ((B.c β).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hf : Tk = (u : Γ(V, ⊤)) * Tl := by
    have := B.f_u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm)
    rwa [f_sec, f_sec] at this
  funext m
  have hm : Tl * uV B β l y h₂ m = Tk * (G.map a).mulVec (uV B α k y h₁) m := by

    rw [← hβ, hG m, map_sum, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, hα, Matrix.map_apply]
    ring
  rw [hf] at hm
  have h3 : Tl * (uV B β l y h₂ m - (u : Γ(V, ⊤)) * (G.map a).mulVec (uV B α k y h₁) m) = 0 := by
    rw [mul_sub, hm]; ring
  have h4 := sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hnz _ (by rwa [mul_comm] at h3))
  rw [Pi.smul_apply, smul_eq_mul, h4, Units.inv_mul_cancel_left]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) : hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _ using 2
  exact CategoryTheory.Functor.map_id _ _

private theorem appLE_top_top {V X : Scheme.{0}} (a : V ⟶ X) (e : (⊤ : V.Opens) ≤ a ⁻¹ᵁ ⊤) :
    a.appLE ⊤ ⊤ e = a.appTop := by
  change a.app ⊤ ≫ V.presheaf.map (homOfLE e).op = a.app ⊤
  exact (congrArg (a.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)

private theorem exists_hom_of_ring {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U) ⟶ Γ(V, ⊤)) :
    ∃ (y : V ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ U), y.appLE U ⊤ h = f := by
  have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₂ : (⊤ : V.Opens) ≤ (V.toSpecΓ ≫ Spec.map f) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨(V.toSpecΓ ≫ Spec.map f) ≫ hU.fromSpec, ?_, ?_⟩
  · exact e₂.trans (Scheme.Hom.preimage_mono _ e₁)
  · rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂, fromSpec_appLE_top]
    have : (V.toSpecΓ ≫ Spec.map f).appLE ⊤ ⊤ e₂ = (Spec.map f).appTop ≫ (Scheme.ΓSpecIso Γ(V, ⊤)).hom := by
      rw [appLE_top_top, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [this, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private theorem hom_eq_of_appLE {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (a b : V ⟶ X)
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b := by
  have key : ∀ (c : V ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ U), ∃ c' : V ⟶ Spec Γ(X, U), c' ≫ hU.fromSpec = c ∧
      c'.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ c.appLE U ⊤ hc := by
    intro c hc
    have hr : Set.range c ⊆ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact hc (Set.mem_univ x)
    refine ⟨IsOpenImmersion.lift hU.fromSpec c hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have e₂ : (⊤ : V.Opens) ≤ (IsOpenImmersion.lift hU.fromSpec c hr) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have := Scheme.Hom.appLE_comp_appLE (IsOpenImmersion.lift hU.fromSpec c hr) hU.fromSpec U ⊤ ⊤ e₁ e₂
    rw [fromSpec_appLE_top, appLE_top_top] at this
    have h2 : (IsOpenImmersion.lift hU.fromSpec c hr ≫ hU.fromSpec).appLE U ⊤
        (by rw [IsOpenImmersion.lift_fac]; exact hc) = c.appLE U ⊤ hc := by
      simp only [IsOpenImmersion.lift_fac]
    rw [← this.trans h2, Iso.hom_inv_id_assoc]
  obtain ⟨a', ha', ea⟩ := key a ha
  obtain ⟨b', hb', eb⟩ := key b hb
  rw [← ha', ← hb', ext_of_isAffine (f := a') (g := b') (by rw [ea, eb, h])]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartLift :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ (α : B.ι) (k : Fin d) {V : Scheme.{0}} (p : V ⟶ W), ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α → ∀ (w : Fin d → Γ(V, ⊤)), w k = 1 → ∃ (y : V ⟶ T) (h : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.c α).C k), y ≫ r = p ∧ uV B α k (y ≫ j) h = w := by
  intro K _ W Z Y q i π D d B T j r hpb α k V p hp w hk
  have ht : ∀ m, ((p ≫ i).appLE (B.V α) ⊤ hp).hom ((B.c α).t m) = 0 := by
    intro m
    have hm : (B.c α).t m ∈ RingHom.ker (i.app (B.V α)).hom := by
      rw [(B.c α).ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.mem_ker.mp hm, map_zero]
  let ψ := MvPolynomial.eval₂Hom (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).u k)
  let φ : MvPolynomial (Fin d) Γ(Z, B.V α) →+* Γ(V, ⊤) :=
    MvPolynomial.eval₂Hom ((p ≫ i).appLE (B.V α) ⊤ hp).hom w
  have hφC : ∀ a, φ (MvPolynomial.C a) = ((p ≫ i).appLE (B.V α) ⊤ hp).hom a := fun a =>
    MvPolynomial.eval₂_C _ _ _
  have hker : RingHom.ker ψ ≤ RingHom.ker φ := by
    change RingHom.ker (MvPolynomial.eval₂Hom _ _) ≤ _
    rw [(B.c α).rel k, Ideal.span_le]
    rintro x (rfl | ⟨m, rfl⟩)
    · simp [φ, hk]
    · change φ _ = 0
      rw [map_sub, map_mul, hφC, hφC, ht, ht, zero_mul, sub_zero]
  let f : Γ(Y, (B.c α).C k) →+* Γ(V, ⊤) := RingHom.liftOfSurjective ψ ((B.c α).surj k) ⟨φ, hker⟩
  have hf : ∀ x, f (ψ x) = φ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φ, hker⟩ x
  obtain ⟨y₀, h₀, hy₀⟩ := exists_hom_of_ring ((B.c α).C_aff k) (CommRingCat.ofHom f)
  have hπ : ⊤ ≤ (y₀ ≫ π) ⁻¹ᵁ B.V α := h₀.trans (Scheme.Hom.preimage_mono _ ((B.c α).C_le k))
  have hc : y₀ ≫ π = p ≫ i := by
    refine hom_eq_of_appLE (B.c α).affine _ _ hπ hp ?_
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ ((B.c α).C_le k) h₀, hy₀]
    ext a
    have := hf (MvPolynomial.C a)
    simpa [ψ, φ] using this
  have hyj : hpb.lift y₀ p hc ≫ j = y₀ := hpb.lift_fst _ _ _
  refine ⟨hpb.lift y₀ p hc, by rw [hyj]; exact h₀, hpb.lift_snd _ _ _, ?_⟩
  have gen : ∀ (y' : V ⟶ Y) (e : y' = y₀) (h : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), uV B α k y' h = w := by
    intro y' e h
    have hy' : Scheme.Hom.appLE y' _ ⊤ h = CommRingCat.ofHom f := by
      subst e
      exact hy₀
    funext m
    have := hf (MvPolynomial.X m)
    simp only [ψ, φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    unfold uV
    rw [hy']
    exact this
  exact gen _ hyj _
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ LocMat B α β (U.ι ≫ p) (M.map U.ι.appTop.hom)) → LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p M h x
  obtain ⟨U, hxU, hL⟩ := h x
  obtain ⟨U', N, hx', hN, h₁, h₂, hU', G, hT, hM⟩ := hL ⟨x, hxU⟩
  have he : (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι = U'.ι ≫ U.ι := U.ι.isoImage_hom_ι U'
  have hU'' : ⊤ ≤ ((U.ι ''ᵁ U').ι ≫ p ≫ i) ⁻¹ᵁ N := by
    rintro ⟨y, z, hz, rfl⟩ _
    have := @hU' (⟨z, hz⟩ : U'.toScheme) trivial
    exact this
  refine ⟨U.ι ''ᵁ U', N, ⟨⟨x, hxU⟩, hx', rfl⟩, hN, h₁, h₂, hU'', G, hT, ?_⟩
  ext a b
  have hinj : ∀ {A C : Scheme.{0}} (e : A ≅ C), Function.Injective e.hom.appTop.hom := by
    intro A C e
    have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
  apply hinj (U.ι.isoImage U')
  have hab := congrFun (congrFun hM a) b
  simp only [Matrix.map_apply] at hab ⊢
  have e₁ : (U.ι.isoImage U').hom.appTop.hom (((U.ι ''ᵁ U').ι).appTop.hom (M a b)) = U'.ι.appTop.hom (U.ι.appTop.hom (M a b)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, he]
  have e₂ : (U.ι.isoImage U').hom.appTop.hom ((((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'').hom (G a b)) = ((U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU').hom (G a b) := by
    have : ((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'' ≫ (U.ι.isoImage U').hom.appTop = (U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU' := by
      have hc : U'.ι ≫ (U.ι ≫ p) ≫ i = (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι ≫ p ≫ i := by
        rw [reassoc_of% he]; simp
      simp only [hc]
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => f.hom (G a b)) this
  rw [e₁, e₂, hab]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_top_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  change _ = f.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

private theorem appLE_comp_appTop' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ N) (h' : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ N) :
    (f ≫ g).appLE N ⊤ h' = g.appLE N ⊤ h ≫ f.appTop := by
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial
  rw [← appLE_top_eq f e]
  exact (Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V' V : Scheme.{0}} (s : V' ⟶ V) (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β (s ≫ p) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B α β V' V s p M h x'
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩ := h (s x')
  have e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i := by
    rw [← Category.assoc (s ∣_ U), morphismRestrict_ι]
    simp only [Category.assoc]
  have hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N := by
    rw [e]
    intro y _
    exact hU (Set.mem_univ ((s ∣_ U) y))
  refine ⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩
  have gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ hf = g.appLE N ⊤ hg := by
    rintro f g rfl _ _
    rfl
  have h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop :=
    (gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)
  have h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a) := by
    intro a
    have e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop := by rw [morphismRestrict_ι]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e2
    exact congrArg (fun φ => φ.hom a) e2
  ext m l
  have h1 := congrFun (congrFun hM m) l
  simp only [Matrix.map_apply] at h1 ⊢
  rw [h3, ← h4, h1]
  rfl
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.uSelf :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k), uV B α k y h k = 1 := by
  intro K _ W Z Y q i π D d B α k V y h
  have hmem : (MvPolynomial.X k - 1 : MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hu : (B.c α).u k k = 1 := by
    have h0 := RingHom.mem_ker.mp hmem
    rw [map_sub, map_one, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at h0
    exact sub_eq_zero.mp h0
  unfold uV
  rw [hu, map_one]
end

section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.kerRes :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h : N ≤ B.V α), RingHom.ker (i.app N).hom = Ideal.span (Set.range (tN B α h)) := by
  intro K _ W Z Y q i π D d B α N hN h
  haveI := B.closed
  have hUV : (⟨N, hN⟩ : Z.affineOpens) ≤ ⟨B.V α, (B.c α).affine⟩ := h
  have key := i.ker.map_ideal hUV
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at key
  change Ideal.map _ (RingHom.ker (i.app (B.V α)).hom) = RingHom.ker (i.app N).hom at key
  rw [(B.c α).ker, Ideal.map_span, ← Set.range_comp] at key
  rw [← key]
  rfl
end
