module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfForallExistsLsumETwoPi
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom

namespace GlobalTheory.Conv

section Values

variable {A : Type} [CommRing A] {Z : Scheme.{0}}

theorem valR_id_top (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR_eq _ _ le_top]
  have h : (𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (((𝟙 (Sp A) : Sp A ⟶ Sp A).appLE ⊤ ⊤ le_top).hom _) = a
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a

theorem valR_spMap_top {O : Type} [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by
  have := valR_spMap β (𝟙 (Sp O)) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)
  rwa [Category.comp_id, valR_id_top] at this

theorem exists_point_of_ringHom {V : Z.Opens} (hV : IsAffineOpen V) (ψ : Γ(Z, V) →+* A) :
    ∃ x : Sp A ⟶ Z, ⊤ ≤ x ⁻¹ᵁ V ∧ ∀ f, valR x V f = ψ f := by
  let x₀ : Sp Γ(Z, V) ⟶ Z := hV.fromSpec
  have h₀ : ⊤ ≤ x₀ ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  refine ⟨spMap ψ ≫ x₀, fun p _ => h₀ (x := spMap ψ p) trivial, fun f => ?_⟩
  rw [valR_spMap ψ x₀ V h₀, valR_eq _ _ h₀]
  congr 1
  have h : hV.fromSpec.appLE V ⊤ h₀ = (Scheme.ΓSpecIso Γ(Z, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self]
    simp [← Functor.map_comp]
  change (Scheme.ΓSpecIso Γ(Z, V)).hom.hom ((hV.fromSpec.appLE V ⊤ h₀).hom f) = f
  rw [h]
  exact (Scheme.ΓSpecIso Γ(Z, V)).inv_hom_id_apply f

end Values

variable {Z : Scheme.{0}}

theorem exists_halfRing_point {O : Type} [CommRing O] (s : Z ⟶ Sp O) [LocallyOfFiniteType s]
    (b : O →+* ℂ) (y : Sp convLaurent ⟶ Z)
    (hy : y ≫ s = spMap ((algebraMap ℂ convLaurent).comp b)) {V : Z.Opens} (hV : IsAffineOpen V)
    (hyV : ⊤ ≤ y ⁻¹ᵁ V) (T₀ : ℝ) :
    ∃ T ≥ T₀, ∃ yT : Sp (halfRing T) ⟶ Z, ⊤ ≤ yT ⁻¹ᵁ V ∧
      spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y ∧
      yT ≫ s = spMap ((algebraMap ℂ (halfRing T)).comp b) := by
  let ρ : O →+* Γ(Z, V) :=
    (s.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  have hρ : ρ.FiniteType := by
    refine (s.finiteType_appLE (isAffineOpen_top _) hV le_top).comp (RingHom.FiniteType.of_surjective _ ?_)
    exact (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective
  have hval : ∀ {A : Type} [CommRing A] (x : Sp A ⟶ Z), ⊤ ≤ x ⁻¹ᵁ V → ∀ a : O,
      valR x V (ρ a) = valR (x ≫ s) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) :=
    fun x hx a => valR_appLE x s ⊤ V le_top _ hx
  letI := ρ.toAlgebra
  haveI : Algebra.FiniteType O Γ(Z, V) := hρ
  obtain ⟨T, hT, ψ, hψ, hψb⟩ := exists_factor_halfRing_over (S := O) b (evalHom y V hyV)
    (RingHom.ext fun a => by
      have := hval y hyV a
      rw [hy, valR_spMap_top, valR_eq _ _ hyV] at this
      exact this) T₀
  obtain ⟨yT, hyT, hv⟩ := exists_point_of_ringHom hV ψ
  refine ⟨T, hT, yT, hyT, ?_, ?_⟩
  · refine point_ext hV (fun p _ => hyT (x := spMap _ p) trivial) hyV fun f => ?_
    rw [valR_spMap _ _ _ hyT, hv, valR_eq _ _ hyV, ← hψ]
    rfl
  · refine point_ext (isAffineOpen_top _) le_top le_top fun f => ?_
    obtain ⟨a, rfl⟩ :=
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv.surjective f
    have := hval yT hyT a
    rw [hv] at this
    exact this.symm.trans ((DFunLike.congr_fun hψb a).trans (valR_spMap_top _ a).symm)

theorem exists_le_preimage_inclusion {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens}
    (hU : ⊤ ≤ (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) ⁻¹ᵁ U) :
    ∃ T', ∃ h : T ≤ T', ⊤ ≤ (spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') ≫ yT) ⁻¹ᵁ U := by
  let p : PrimeSpectrum (halfRing T) :=
    spMap (halfIncl T : halfRing T →+* convLaurent) (default : PrimeSpectrum convLaurent)
  have hp : p ∈ (show Set (PrimeSpectrum (halfRing T)) from (yT ⁻¹ᵁ U).carrier) :=
    hU (x := (default : PrimeSpectrum convLaurent)) trivial
  obtain ⟨_, ⟨r, rfl⟩, hr, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp (yT ⁻¹ᵁ U).isOpen
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr p.asIdeal.zero_mem
  obtain ⟨T', h, hu⟩ := exists_isUnit_halfRing hr0
  refine ⟨T', h, fun q _ => hle (a := spMap (Subalgebra.inclusion (halfRing_mono h) :
      halfRing T →+* halfRing T') q) fun hq => ?_⟩
  exact q.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)

def halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) (w : ℂ) : Sp ℂ ⟶ Z :=
  if hw : T < w.im then spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT
  else spMap (ev T (((T + 1 : ℝ) : ℂ) * Complex.I) (by simp) : halfRing T →+* ℂ) ≫ yT

theorem halfCurve_eq {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {w : ℂ} (hw : T < w.im) :
    halfCurve yT w = spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT := dif_pos hw

theorem halfCurve_comp {T : ℝ} {Z' : Scheme.{0}} (yT : Sp (halfRing T) ⟶ Z) (j : Z ⟶ Z') (w : ℂ) :
    halfCurve (yT ≫ j) w = halfCurve yT w ≫ j := by
  unfold halfCurve
  split_ifs <;> rw [Category.assoc]

theorem halfCurve_inclusion {T T' : ℝ} (h : T ≤ T') (yT : Sp (halfRing T) ⟶ Z) {w : ℂ}
    (hw : T' < w.im) :
    halfCurve (spMap (Subalgebra.inclusion (halfRing_mono h) : halfRing T →+* halfRing T') ≫ yT) w =
      halfCurve yT w := by
  rw [halfCurve_eq _ hw, halfCurve_eq _ (h.trans_lt hw), ← Category.assoc, ← spMap_comp]
  rfl

theorem valAt'_halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {U : Z.Opens} (hU : ⊤ ≤ yT ⁻¹ᵁ U)
    {w : ℂ} (hw : T < w.im) :
    ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧ ∀ f, valAt' (halfCurve yT w) U f = ev T w hw (valR yT U f) := by
  rw [halfCurve_eq _ hw]
  exact ⟨fun p _ => hU (x := spMap _ p) trivial, fun f => valR_spMap _ yT U hU f⟩

theorem isHolTo_halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) :
    IsHolTo {w : ℂ | T < w.im} (halfCurve yT) := by
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  refine isHolTo_of_holAt ho fun z hz => ?_
  have h : HolAt (halfCurve (𝟙 (Sp (halfRing T)))) z := by
    refine holAt_of_affine (isAffineOpen_top _) le_top (Eventually.of_forall fun _ => le_top)
      fun g => ?_
    exact (differentiableOn_of_eq_ev (valR (𝟙 (Sp (halfRing T))) ⊤ g)
      fun w hw => (valAt'_halfCurve (𝟙 _) le_top hw).2 g).differentiableAt (ho.mem_nhds hz)
  have := h.comp yT
  simpa only [← halfCurve_comp, Category.id_comp] using this

theorem exists_valAt'_halfCurve {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {U : Z.Opens}
    (hU : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ T' ≥ T, (∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U) ∧
      ∀ f : Γ(Z, U), ∃ hf : ((valR y U f : convLaurent) : ℂ⸨X⸩) ∈ halfRing T',
        ∀ (w : ℂ) (hw : T' < w.im), valAt' (halfCurve yT w) U f = ev T' w hw ⟨_, hf⟩ := by
  subst hy
  obtain ⟨T', h, hU'⟩ := exists_le_preimage_inclusion yT hU
  refine ⟨T', h, fun w hw => ?_, fun f => ?_⟩
  · rw [← halfCurve_inclusion h yT hw]
    exact (valAt'_halfCurve _ hU' hw).1
  · have e := valR_spMap (halfIncl T' : halfRing T' →+* convLaurent) _ U hU' f
    rw [← Category.assoc, ← spMap_comp] at e
    have e' : ((valR (spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT) U f : convLaurent) :
        ℂ⸨X⸩) = (valR (spMap (Subalgebra.inclusion (halfRing_mono h) :
          halfRing T →+* halfRing T') ≫ yT) U f : halfRing T') :=
      congrArg (fun x : convLaurent => (x : ℂ⸨X⸩)) e
    refine ⟨e' ▸ Subtype.property _, fun w hw => ?_⟩
    rw [← halfCurve_inclusion h yT hw, (valAt'_halfCurve _ hU' hw).2]
    exact ev_congr hw hw e'.symm

theorem exists_sumsAt_halfCurve {T : ℝ} {yT : Sp (halfRing T) ⟶ Z} {y : Sp convLaurent ⟶ Z}
    (hy : spMap (halfIncl T : halfRing T →+* convLaurent) ≫ yT = y) {χ : Sp ℂ⟦X⟧ ⟶ Z}
    {F : Type} [Field F] (ι : ℂ⸨X⸩ →+* F)
    (hχ : spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) ≫ χ =
      spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y)
    {U : Z.Opens} (hU : ⊤ ≤ χ ⁻¹ᵁ U) :
    ∃ T' ≥ T, ∀ w : ℂ, T' < w.im → ⊤ ≤ halfCurve yT w ⁻¹ᵁ U ∧
      ∀ f : Γ(Z, U), SumsAt (valR χ U f) w (valAt' (halfCurve yT w) U f) := by
  have hyU : ⊤ ≤ y ⁻¹ᵁ U := by
    intro p _
    have h1 : ⊤ ≤ (spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) ≫ y) ⁻¹ᵁ U := by
      rw [← hχ]
      exact fun q _ => hU (x := spMap _ q) trivial
    obtain rfl : p = spMap (ι.comp (algebraMap convLaurent ℂ⸨X⸩)) (default : PrimeSpectrum F) :=
      Subsingleton.elim (α := PrimeSpectrum convLaurent) _ _
    exact h1 (x := (default : PrimeSpectrum F)) trivial
  obtain ⟨T', hT, h₁, h₂⟩ := exists_valAt'_halfCurve hy hyU
  refine ⟨T', hT, fun w hw => ⟨h₁ w hw, fun f => ?_⟩⟩
  obtain ⟨hf, hv⟩ := h₂ f
  rw [hv w hw]
  refine sumsAt_ev_of_eq hw (ι.injective ?_)
  have e := valR_spMap (ι.comp (algebraMap ℂ⟦X⟧ ℂ⸨X⸩)) χ U hU f
  rw [hχ, valR_spMap _ y U hyU] at e
  exact e.symm

end GlobalTheory.Conv
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

noncomputable section

namespace GlobalTheory.HolHomOnto

open GlobalTheory.TangentOrigin GlobalTheory.HolHom

theorem exists_coords {Y : Scheme.{0}} (s : Y ⟶ Sp ℂ) [Smooth s] (x : Sp ℂ ⟶ Y) (hx : x ≫ s = 𝟙 _) :
    ∃ (n : ℕ) (U : Y.Opens) (t : Fin n → Γ(Y, U)) (W : Set (Fin n → ℂ)),
      ⊤ ≤ x ⁻¹ᵁ U ∧ IsOpen W ∧ 0 ∈ W ∧
      (∀ w ∈ W, ∃ p : Sp ℂ ⟶ Y, p ≫ s = 𝟙 _ ∧ ⊤ ≤ p ⁻¹ᵁ U ∧ ∀ i, valAt' p U (t i) = w i) ∧
      ∀ v v' : Sp (DualNumber ℂ) ⟶ Y, v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) →
        v' ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap fstC ≫ v = x → spMap fstC ≫ v' = x →
        (∀ i, (valR v U (t i)).snd = (valR v' U (t i)).snd) → v = v' := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s (x (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (x (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (x (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(Y, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  let c : ℂ →+* Γ(Y, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn s U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have hconst : ∀ {R : Type} [CommRing R] (ψ : ℂ →+* R) (y : Sp R ⟶ Y) (hy : ⊤ ≤ y ⁻¹ᵁ U), y ≫ s = spMap ψ →
      ∀ a, evalPt y U hy (c a) = ψ a := by
    intro R _ ψ y hy hys a
    rw [← hcc, evalPt_constFn]
    exact (congrArg (fun y : Sp R ⟶ Sp ℂ => evalPt y ⊤ le_rfl
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) hys).trans (evalPt_spMap _ a)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := (le_preimage_iff x U).2 hp
  have hxc : ∀ a, evalPt x U hxU (c a) = a := hconst (RingHom.id ℂ) x hxU (hx.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing c hc (evalPt x U hxU) hxc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(Y, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) ℂ) Γ(Y, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(Y, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin n) ℂ) Γ(Y, U) := hφ
  let eA : Γ(Y, U) →ₐ[ℂ] ℂ := { evalPt x U hxU with commutes' := hxc }
  obtain ⟨W, σ, m, f, ε, hW, hW0, -, -, -, hσt, -⟩ :=
    exists_holomorphic_section_of_etale n Γ(Y, U) eA hφ0
  refine ⟨n, U, fun i => φ (MvPolynomial.X i), W, hxU, hW, hW0, fun w hw => ?_, fun v v' hv hv' h0 h0' ht => ?_⟩
  · obtain ⟨p, hpU, hpσ⟩ := exists_evalPt_eq hU (σ w).toRingHom
    refine ⟨p, ?_, hpU, fun i => ?_⟩
    · refine (eq_spMap_of_evalPt _ (RingHom.id ℂ) fun a => ?_).trans (Spec.map_id _)
      rw [← evalPt_constFn s p U hpU, hpσ, hcc]
      exact (σ w).commutes a
    · rw [valAt'_eq_evalPt _ _ hpU, hpσ]
      exact hσt w hw i
  · have hvU := (le_preimage_dual_iff h0 U).2 hxU
    have hvU' := (le_preimage_dual_iff h0' U).2 hxU
    have e1 : ∀ f, valR v U f = evalPt v U hvU f := valR_eq _ _ hvU
    have e2 : ∀ f, valR v' U f = evalPt v' U hvU' f := valR_eq _ _ hvU'
    have f1 : ∀ f, (evalPt v U hvU f).fst = evalPt x U hxU f := fun f => by
      rw [← e1, fst_valR h0 hxU, valAt'_eq_evalPt]
    have f2 : ∀ f, (evalPt v' U hvU' f).fst = evalPt x U hxU f := fun f => by
      rw [← e2, fst_valR h0' hxU, valAt'_eq_evalPt]
    let D : Γ(Y, U) →+ ℂ :=
      { toFun := fun f => (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd
        map_zero' := by simp
        map_add' := fun f f' => by
          simp only [map_add (f := _), TrivSqZeroExt.snd_add]
          ring }
    have hD : ∀ f, D f = (evalPt v U hvU f).snd - (evalPt v' U hvU' f).snd := fun _ => rfl
    have hz : D = 0 := by
      refine HolChart.derivation_eq_zero φ hφ (evalPt x U hxU) D (fun a => ?_) (fun f f' => ?_) fun i => ?_
      · rw [hD, hφc', hconst _ v hvU hv, hconst _ v' hvU' hv', sub_self]
      · rw [hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, f1, f1, f2, f2]
        ring
      · rw [hD, ← e1, ← e2, ht, sub_self]
    refine ext_evalPt hU hvU hvU' (RingHom.ext fun f => TrivSqZeroExt.ext ((f1 f).trans (f2 f).symm) ?_)
    have := hD f
    rw [hz] at this
    exact sub_eq_zero.1 this.symm

theorem exists_isDerivAt_of_surjective : ∀ (G : Over (Sp ℂ)) [GrpObj G] (y : Sp ℂ ⟶ Sp ℂ), y = 𝟙 _ → Smooth G.hom → ∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) → ∀ v : Sp (DualNumber ℂ) ⟶ G.left, v ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = (e 0).left → ∃ w, GlobalTheory.HolHom.IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w v := by
  intro G _ y hy hs g e he hsurj hol v hv hv0
  subst hy
  obtain ⟨n, U, t, W, h0, hW, hW0, hp, hext⟩ := exists_coords G.hom (e 0).left (Over.w (e 0))
  have hA := holAt_of_isHolTo hol (Set.mem_univ 0)
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi fun i => (fderiv ℂ (fun z => valAt' (e z).left U (t i)) 0).toLinearMap
  have hover : ∀ {w u}, IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u →
      u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := fun hu =>
    (IsDerivAt.over (a := e) hu).trans (Category.comp_id _)
  have key : ∀ (w : Fin g → ℂ) (u : Sp (DualNumber ℂ) ⟶ G.left), u ≫ G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) →
      spMap fstC ≫ u = (e 0).left → (L w = fun i => (valR u U (t i)).snd) →
      IsDerivAt (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) 0 w u := by
    intro w u hu hu0 hL
    obtain ⟨u', hu'⟩ := hA.exists_isDerivAt w
    have : u = u' := hext u u' hu (hover hu') hu0 hu'.1 fun i =>
      (congrFun hL i).symm.trans (hu'.2 U h0 (t i)).symm
    exact this ▸ hu'
  suffices hL : Function.Surjective L by
    obtain ⟨w, hw⟩ := hL fun i => (valR v U (t i)).snd
    exact ⟨w, key w v hv hv0 hw⟩
  obtain ⟨ρ, hρ⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let P : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (ρ ∘ₗ L.rangeRestrict)
  have hLP : ∀ z, L (P z) = L z := fun z =>
    congrArg Subtype.val (DFunLike.congr_fun hρ (L.rangeRestrict z))
  have hfac : e = fun z => e (P z) := by
    refine eq_of_fderiv_eq he (fun z w => by rw [map_add (f := _), he]) hol
      (isHolTo_of_holAt isOpen_univ fun z _ =>
        (holAt_of_isHolTo hol (Set.mem_univ (P z))).precomp P.differentiableAt) fun V hV f => ?_
    ext1 z
    have h1 : HasFDerivAt (fun z => valAt' (e z).left V f) (fderiv ℂ (fun z => valAt' (e z).left V f) 0) (P 0) := by
      rw [map_zero]; exact ((hA V hV).2 f).hasFDerivAt
    refine Eq.trans ?_ (congrArg (· z) (h1.comp 0 P.hasFDerivAt).fderiv).symm
    obtain ⟨u, hu⟩ := hA.exists_isDerivAt z
    have hu' := key (P z) u (hover hu) hu.1 ((hLP z).trans (funext fun i => (hu.2 U h0 (t i)).symm))
    exact (hu.2 V hV f).symm.trans (hu'.2 V hV f)
  have hol' : IsHolTo Set.univ (fun r : LinearMap.range L => (show Sp ℂ ⟶ G.left from (e (ρ r)).left)) :=
    isHolTo_of_holAt isOpen_univ fun r _ =>
      (holAt_of_isHolTo hol (Set.mem_univ (ρ r))).precomp (LinearMap.toContinuousLinearMap ρ).differentiableAt
  rw [← LinearMap.range_eq_top]
  by_contra hne
  have hlt : Module.finrank ℂ (LinearMap.range L) < n := by
    simpa using Submodule.finrank_lt hne
  have hnull := AffinePoints.volume_image_eq_zero_of_finrank_lt hlt
    (f := fun r i => valAt' (e (ρ r)).left U (t i)) (differentiableOn_pi.2 fun i => (hol' U (t i)).2)
  refine (hW.measure_pos MeasureTheory.volume ⟨0, hW0⟩).ne' (MeasureTheory.measure_mono_null (fun w hw => ?_) hnull)
  obtain ⟨p, hps, hpU, hpt⟩ := hp w hw
  obtain ⟨z, hz⟩ := hsurj (Over.homMk p hps)
  have hz' : (e (ρ (L.rangeRestrict z))).left = p :=
    congrArg (·.left) ((congrFun hfac z).symm.trans hz)
  refine ⟨L.rangeRestrict z, ⟨trivial, ?_⟩, funext fun i => ?_⟩
  · subst hz'
    exact hpU
  · subst hz'
    exact hpt i

end GlobalTheory.HolHomOnto
end
end

section

noncomputable section

namespace GlobalTheory.ThetaShiftProofs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem exists_unit_gm_spMap {A F : Type} [CommRing A] [Field F] {X : Scheme.{0}} (f : A →+* F) (x : Sp A ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (z : Sp F) :
    ∃ u : Aˣ, (gm (spMap f ≫ x) z U a).val = toStk z (f u) := by
  let g : Γ(X, U) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom
  refine ⟨Units.map g.toMonoidHom a, ?_⟩
  have hz : (spMap f ≫ x) z ∈ U := h (show spMap f z ∈ (⊤ : (Sp A).Opens) from trivial)
  rw [← toStk_valF _ U z hz]
  congr 1
  have ht := (top_le_iff_mem (spMap f ≫ x) U z).2 hz
  rw [valF, dite_eq_left ht]
  have e1 : (spMap f ≫ x).appLE U ⊤ ht = x.appLE U ⊤ h ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have e3 := congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom a.val)) e2
  rw [e1]
  exact e3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k}

end GlobalTheory.ThetaShiftProofs
end
end
