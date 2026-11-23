module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

section

noncomputable section
open Matrix

namespace LateralTheory.CohomologicalPurity.MatPf

theorem gens {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A)
    (h : Ideal.span (Set.range x) ≤ Ideal.span (Set.range y)) :
    ∃ N : Matrix (Fin d) (Fin d) A, x = N *ᵥ y := by
  have : ∀ i, ∃ c : Fin d → A, ∑ j, c j * y j = x i := fun i =>
    (Ideal.mem_span_range_iff_exists_fun).1 (h (Ideal.subset_span ⟨i, rfl⟩))
  choose c hc using this
  exact ⟨Matrix.of c, funext fun i => by simp [mulVec, dotProduct, hc]⟩

theorem red {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A) (N N' T : Matrix (Fin d) (Fin d) A)
    (hy : y = N *ᵥ x) (hx : x = N' *ᵥ y) : y = (N + T * (1 - N' * N)) *ᵥ x := by
  have : (1 - N' * N) *ᵥ x = 0 := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← hy, ← hx, sub_self]
  rw [add_mulVec, ← mulVec_mulVec, this, mulVec_zero, add_zero, hy]

theorem glue_dom (hD : ∀ (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D),
    N' * N + E = 1 → ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0) : LateralTheory.CohomologicalPurity.Cl.LeafMat := by
  intro d A _ x y hxy p
  obtain ⟨N, hN⟩ := gens y x hxy.ge
  obtain ⟨N', hN'⟩ := gens x y hxy.le
  let f := Ideal.Quotient.mk p.asIdeal
  obtain ⟨T₀, hT₀⟩ := hD d (A ⧸ p.asIdeal) (f.mapMatrix N) (f.mapMatrix (1 - N' * N)) (f.mapMatrix N')
    (by rw [← map_mul, ← map_add (f := _), add_sub_cancel, map_one])
  choose T hT using fun i j => Ideal.Quotient.mk_surjective (I := p.asIdeal) (T₀ i j)
  refine ⟨N + Matrix.of T * (1 - N' * N), ?_, red x y N N' _ hN hN'⟩
  intro hm
  apply hT₀
  have h1 : f.mapMatrix (Matrix.of T) = T₀ := by ext i j; simp [f, hT]
  have := RingHom.map_det f (N + Matrix.of T * (1 - N' * N))
  rw [map_add (f := _), map_mul, h1, (Ideal.Quotient.eq_zero_iff_mem).2 hm] at this
  exact this.symm

theorem fld {d : ℕ} {k : Type} [Field k] (N E N' : Matrix (Fin d) (Fin d) k) (h : N' * N + E = 1) :
    ∃ T : Matrix (Fin d) (Fin d) k, ∀ s : k, s ≠ 0 → (N + (s • T) * E).det ≠ 0 := by
  classical
  let n := Matrix.toLin' N
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range n)
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker n)
  have hr : Module.finrank k (LinearMap.ker n) = Module.finrank k C := by
    have h1 := LinearMap.finrank_range_add_finrank_ker n
    have h2 := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hr
  let t : (Fin d → k) →ₗ[k] (Fin d → k) :=
    C.subtype ∘ₗ e.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl _ _ hK
  refine ⟨LinearMap.toMatrix' t, fun s hs hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  apply hv0
  have hE : E = 1 - N' * N := by rw [← h]; abel
  rw [add_mulVec, ← mulVec_mulVec, smul_mulVec, LinearMap.toMatrix'_mulVec] at hv
  have htC : ∀ w, t w ∈ C := fun w => (e _).2
  have hnv : n v = 0 := by
    have hm : n v ∈ C := by
      have : n v = -(s • t (E *ᵥ v)) := eq_neg_of_add_eq_zero_left (by simpa [n] using hv)
      rw [this]; exact C.neg_mem (C.smul_mem s (htC _))
    exact (Submodule.disjoint_def.1 hC.disjoint) _ (LinearMap.mem_range_self n v) hm
  have hNv : N *ᵥ v = 0 := by simpa [n] using hnv
  have hw : E *ᵥ v = v := by
    rw [hE, sub_mulVec, one_mulVec, ← mulVec_mulVec, hNv, mulVec_zero, sub_zero]
  rw [hw, hNv, zero_add, smul_eq_zero] at hv
  have htv : t v = 0 := hv.resolve_left hs
  have hker : v ∈ LinearMap.ker n := hnv
  have hp : Submodule.linearProjOfIsCompl _ _ hK v = ⟨v, hker⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hker⟩
  have : e ⟨v, hker⟩ = 0 := by
    apply Subtype.ext
    have := htv
    simp only [t, LinearMap.comp_apply, hp] at this
    exact this
  have he : e ⟨v, hker⟩ = e 0 := this.trans (e.toLinearMap.map_zero).symm
  have := congrArg Subtype.val (e.injective he)
  simpa using this

theorem dom (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D)
    (h : N' * N + E = 1) : ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0 := by
  classical
  let g := algebraMap D (FractionRing D)
  obtain ⟨T, hT⟩ := fld (g.mapMatrix N) (g.mapMatrix E) (g.mapMatrix N')
    (by rw [← map_mul, ← map_add (f := _), h, map_one])
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D)
    (fun ij : Fin d × Fin d => T ij.1 ij.2)
  choose T' hT' using fun i j => hb (i, j)
  have h1 : g.mapMatrix (Matrix.of T') = g b • T := by
    ext i j; simp [g, hT', Algebra.smul_def]
  have hne : g b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Matrix.of T', fun h0 => hT (g b) hne ?_⟩
  have := RingHom.map_det g (N + Matrix.of T' * E)
  rw [h0, map_zero, map_add (f := _), map_mul, h1] at this
  exact this.symm

end LateralTheory.CohomologicalPurity.MatPf

theorem LateralTheory.CohomologicalPurity.Cl.LeafMat_of : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.MatPf.glue_dom LateralTheory.CohomologicalPurity.MatPf.dom
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

def LeafCmpNb : Prop := ∀ (X : Scheme.{0}) (B B₀ : Type) [CommRing B] [CommRing B₀] (w : Spec (CommRingCat.of B) ⟶ X)
  (w₀ : Spec (CommRingCat.of B₀) ⟶ X), IsOpenImmersion w₀ → ∀ y, w y ∈ Set.range w₀ →
  ∃ (C : Type) (_ : CommRing C) (φ : B →+* C) (ψ : B₀ →+* C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ w = Spec.map (CommRingCat.ofHom ψ) ≫ w₀

def LeafCmpId : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C),
  Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w → F.I.map φ = F₀.I.map ψ

theorem spec_comp_ofHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

theorem LeafCmp_of (hMat : LeafMat) (hNb : LeafCmpNb) (hId : LeafCmpId) : LeafCmp := by
  intro d P F F₀ h₀ y hy
  obtain ⟨C, _, φ, ψ, ho, ⟨z, rfl⟩, e⟩ := hNb P.X F.B F₀.B F.w F₀.w h₀ y hy
  have hI := hId d P F F₀ C φ ψ e
  obtain ⟨M, hdet, hM⟩ := hMat d C (ψ ∘ F₀.x) (φ ∘ F.x)
    (by rw [span_comp, span_comp, F.hx, F₀.hx, hI]) z
  let g : C := M.det
  let l : C →+* Localization.Away g := algebraMap C (Localization.Away g)
  have hl : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) g
  refine ⟨Localization.Away g, inferInstance, l.comp φ, l.comp ψ, M.map l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_comp_ofHom φ l]; infer_instance
  · have hr : z ∈ Set.range (PrimeSpectrum.comap l) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hdet
    obtain ⟨z', hz'⟩ := hr
    refine ⟨show Spec (CommRingCat.of (Localization.Away g)) from z', ?_⟩
    rw [spec_comp_ofHom φ l]
    show (Spec.map (CommRingCat.ofHom φ)) ((Spec.map (CommRingCat.ofHom l)) z') = _
    exact congrArg (Spec.map (CommRingCat.ofHom φ)) hz'
  · rw [spec_comp_ofHom φ l, spec_comp_ofHom ψ l, Category.assoc, Category.assoc, e]
  · rw [← Ideal.map_map, ← Ideal.map_map, hI]
  · change IsUnit (l.mapMatrix M).det
    rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit g
  · funext j
    change l (φ (F.x j)) = _
    rw [show φ (F.x j) = (φ ∘ F.x) j from rfl, hM, RingHom.map_mulVec]
    rfl

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

abbrev resO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (V : X.Opens) (n i : ℤ) :
    Hs q (opn U) n i →+ Hs q (opn (V.ι ⁻¹ᵁ U)) n i :=
  Hs.pull q (opnMap V.ι (V.ι ⁻¹ᵁ U) U le_rfl) n i

def LocVanO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ (x : X) (W : X.Opens), x ∈ W →
  ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧ ∀ n < m, Subsingleton (Hs q (opn (V.ι ⁻¹ᵁ U)) n i)

def SepO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ s : Hs q (opn U) m i,
  (∀ x : X, x ∉ U → ∃ V : X.Opens, x ∈ V ∧ resO q U V m i s = 0) → s = 0

def GlueO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop :=
  ∀ (A : Type) (V : A → X.Opens) (s : ∀ a, Hs q (opn ((V a).ι ⁻¹ᵁ U)) m i), (∀ x : X, x ∉ U → ∃ a, x ∈ V a) →
  (∀ a b, ∀ x ∈ V a, x ∈ V b → x ∉ U → ∃ (T : X.Opens) (ha : T ≤ V a) (hb : T ≤ V b)
    (ha' : T.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((V a).ι ⁻¹ᵁ U)) (hb' : T.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((V b).ι ⁻¹ᵁ U)),
    x ∈ T ∧ Hs.pull q (opnMap (X.homOfLE ha) _ _ ha') m i (s a) = Hs.pull q (opnMap (X.homOfLE hb) _ _ hb') m i (s b)) →
  ∃ c, ∀ a, resO q U (V a) m i c = s a

def LeafDescOSep : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → SepO q U m i

def LeafDescOGlue : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → GlueO q U m i

def LeafPcVan : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), LocVan q U m i → LocVanO q U m i

def LeafPcSep : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), SepO q U m i → Sep q U m i

def LeafPcGlue : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), GlueO q U m i → Glue q U m i

theorem opnMap_id {X : Scheme.{0}} (U : X.Opens) (h) : opnMap (𝟙 X) U U h = 𝟙 _ := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map (𝟙 _)
    congr 1
    exact (Scheme.Hom.resLE_id (X := X) (V := U) (V' := U) le_rfl).trans (Scheme.homOfLE_rfl _ _)
  · exact sch.map_id X

theorem dbl_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
   apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = _
    rw [inl_map]; erw [Category.id_comp]
  · change dbl.inr _ ≫ _ = _
    rw [dbl.inr_map]; erw [Category.id_comp]

theorem Hs_pull_id (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (h) (n i : ℤ) (c : Hs q (opn U) n i) :
    Hs.pull q (opnMap (𝟙 X) U U h) n i c = c := by
  apply Subtype.ext
  rw [opnMap_id]
  change pull _ (dbl.map _) _ n c.1 = c.1
  rw [dbl_id, pull_id]

section
variable {q : ℕ} {X : Scheme.{0}} {U : X.Opens}

instance (p : Pc U) : IsOpenImmersion p.j := p.op

theorem pc_le (p : Pc U) : p.V ≤ p.j.isoOpensRange.hom ⁻¹ᵁ (p.j.opensRange.ι ⁻¹ᵁ U) := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.hom ≫ p.j.opensRange.ι) y ∈ U
  rw [Scheme.Hom.isoOpensRange_hom_ι]; exact hy

theorem pc_le' (p : Pc U) : p.j.opensRange.ι ⁻¹ᵁ U ≤ p.j.isoOpensRange.inv ⁻¹ᵁ p.V := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.inv ≫ p.j) y ∈ U
  rw [Scheme.Hom.isoOpensRange_inv_comp]; exact hy

theorem pc_bij (p : Pc U) (n i : ℤ) :
    Function.Bijective (Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i) := by
  refine ⟨Function.LeftInverse.injective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_,
    Function.RightInverse.surjective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_⟩
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.inv_hom_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.hom_inv_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)

theorem pc_res (p : Pc U) (n i : ℤ) (s : Hs q (opn U) n i) :
    p.res q n i s = Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i (resO q U p.j.opensRange n i s) :=
  (pull_pull _ _ (Scheme.Hom.isoOpensRange_hom_ι p.j) _ _ _ _ _ _ n i s).symm
end

theorem LeafPcVan_pf : LeafPcVan := by
  intro q X U m i hL x W hx
  obtain ⟨p, hxp, hpW, hs⟩ := hL x W hx
  refine ⟨p.j.opensRange, fun y hy => hpW hy, hxp, fun n hn => ?_⟩
  have := hs n hn
  exact (pc_bij p n i).1.subsingleton

theorem LeafPcSep_pf : LeafPcSep := by
  intro q X U m i hS s hs
  apply hS s
  intro x hx
  obtain ⟨p, hxp, h0⟩ := hs x hx
  refine ⟨p.j.opensRange, hxp, ?_⟩
  apply (pc_bij p m i).1
  rw [← pc_res, h0, map_zero]

theorem LeafDesc_of (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) (hPG : LeafPcGlue) :
    LeafDesc := by
  intro q X U m i hL
  have hO := LeafPcVan_pf q U m i hL
  exact ⟨LeafPcSep_pf q U m i (hS hD hF q U m i hO), hPG q U m i (hG hD hF q U m i hO)⟩

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section

namespace LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity

theorem inj_sq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) (y : A)
    (hy : φ y ∈ (I ^ 2).map φ) : y ∈ I ^ 2 := by
  let _ := φ.toAlgebra
  have _ : Algebra.Etale A B := h.1
  let e := RingEquiv.ofBijective _ h.2
  let f : B →ₐ[A] A ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))
      commutes' := fun a => by
        change e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk I a
        rw [e.symm_apply_eq]
        rfl }
  let g : A ⧸ I ^ 2 →ₐ[A] A ⧸ I := Ideal.Quotient.factorₐ A (Ideal.pow_le_self two_ne_zero)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)
  have hn : IsNilpotent (RingHom.ker (g : A ⧸ I ^ 2 →+* A ⧸ I)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, ← le_bot_iff]
    refine le_trans (le_of_eq (pow_two _)) ?_
    refine Ideal.mul_le.mpr fun x hx z hz => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hz' : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hx' hz'
  let σ := Algebra.FormallySmooth.liftOfSurjective f g hg hn
  have hσ : ∀ a, σ (φ a) = Ideal.Quotient.mk (I ^ 2) a := fun a => σ.commutes a
  have hc : (σ : B →+* A ⧸ I ^ 2).comp φ = Ideal.Quotient.mk (I ^ 2) := RingHom.ext hσ
  have h0 := Ideal.mem_map_of_mem (σ : B →+* A ⧸ I ^ 2) hy
  rw [Ideal.map_map, hc, Ideal.map_quotient_self, Ideal.mem_bot] at h0
  change σ (φ y) = 0 at h0
  rw [hσ] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem approx {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ) (J : Ideal A) (T : Set B)
    (hT : ∀ t ∈ T, t ∈ I.map φ ∧ ∃ c ∈ J, t - φ c ∈ I.map φ ^ 2) :
    ∀ z ∈ Ideal.span T, ∃ c ∈ J, z - φ c ∈ I.map φ ^ 2 := by
  have hle : Ideal.span T ≤ I.map φ := Ideal.span_le.mpr fun t ht => (hT t ht).1
  intro z hz
  induction hz using Submodule.span_induction with
  | mem t ht => exact (hT t ht).2
  | zero => exact ⟨0, J.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨c, hc, hxc⟩ := ihx
    obtain ⟨c', hc', hyc⟩ := ihy
    refine ⟨c + c', J.add_mem hc hc', ?_⟩
    have : x + y - φ (c + c') = (x - φ c) + (y - φ c') := by rw [map_add (f := _)]; ring
    rw [this]; exact Ideal.add_mem _ hxc hyc
  | smul b x hx ih =>
    obtain ⟨c, hc, hxc⟩ := ih
    obtain ⟨c', hbc⟩ := hs b
    refine ⟨c' * c, J.mul_mem_left _ hc, ?_⟩
    have : b • x - φ (c' * c) = (b - φ c') * x + φ c' * (x - φ c) := by
      rw [map_mul, smul_eq_mul]; ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hxc)
    rw [pow_two]
    exact Ideal.mul_mem_mul hbc (hle hx)

end LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity.GenRingPf in
theorem LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := by
  intro d A _ I hI hC
  obtain ⟨B, _, φ, ψ, hN, _, hspan, _⟩ := hC
  have hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ := by
    intro b
    obtain ⟨x, hx⟩ := hN.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨c, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have := (I.map φ).neg_mem hx
    rwa [neg_sub] at this
  have hI1 : ∀ z ∈ I.map φ, ∃ c ∈ I, z - φ c ∈ I.map φ ^ 2 :=
    approx φ I hs I (φ '' I) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := ht
      exact ⟨Ideal.mem_map_of_mem _ hi, i, hi, by simp⟩)
  have hX : ∀ j, ∃ c ∈ I, ψ (MvPolynomial.X j) - φ c ∈ I.map φ ^ 2 := fun j =>
    hI1 _ (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha hax using hX
  have hle : I ≤ Ideal.span (Set.range a) ⊔ I • I := by
    intro y hy
    have hy' : φ y ∈ Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) := hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc, hyc⟩ := approx φ I hs (Ideal.span (Set.range a)) _ (fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact ⟨hspan ▸ Ideal.subset_span ⟨j, rfl⟩, a j, Ideal.subset_span ⟨j, rfl⟩, hax j⟩) _ hy'
    have h2 : y - c ∈ I ^ 2 := inj_sq φ I hN _ (by rw [map_sub, Ideal.map_pow]; exact hyc)
    have : y = c + (y - c) := by ring
    rw [this]
    refine Submodule.add_mem_sup hc ?_
    rw [Ideal.smul_eq_mul, ← pow_two]; exact h2
  obtain ⟨r, hr, hrle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hI le_rfl hle
  refine ⟨a, r, hr, ha, fun y hy => ?_⟩
  have := hrle (Submodule.smul_mem_pointwise_smul y r I hy)
  simpa [smul_eq_mul] using this
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.NbPf

variable {A B : Type} [CommRing A] [CommRing B]

def psi (φ : A →+* B) (I : Ideal A) (hb : Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) :
    B →+* A ⧸ I :=
  (RingEquiv.ofBijective _ hb).symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))

theorem psi_comp (φ : A →+* B) (I : Ideal A) (hb) : (psi φ I hb).comp φ = Ideal.Quotient.mk I := by
  ext a
  simp only [psi, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [RingEquiv.symm_apply_eq]
  simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]

theorem isPushout_psi (φ : A →+* B) (I : Ideal A) (hb) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (psi φ I hb)) (𝟙 (CommRingCat.of (A ⧸ I))) := by
  refine ⟨⟨by ext a; simpa using congrArg (fun f => f a) (psi_comp φ I hb)⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => s.inr) ?_ ?_ ?_⟩⟩
  · intro s
    have hk : I.map φ ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro i hi
      have := congrArg (fun f => f.hom i) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this, Ideal.Quotient.eq_zero_iff_mem.mpr hi]
    ext b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (psi φ I hb b)
    have e1 : Ideal.Quotient.mk (I.map φ) (φ a) = Ideal.Quotient.mk (I.map φ) b := by
      have : (RingEquiv.ofBijective _ hb) (psi φ I hb b) = Ideal.Quotient.mk (I.map φ) b := by
        simp [psi]
      rw [← this, ← ha]; simp [RingEquiv.ofBijective_apply, Ideal.quotientMap_mk]
    rw [Ideal.Quotient.eq] at e1
    have e2 : s.inl.hom (φ a) = s.inl.hom b := by
      have := hk e1; rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this; exact this
    have e3 := congrArg (fun f => f.hom a) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e3
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ← ha]
    rw [← e2, e3]
  · intro s; simp
  · intro s m _ h2; simpa using h2

theorem nb (hE : LeafExc) : Cl.LeafNb := by
  intro hA1 q A B _ _ φ I J hN hJ h
  subst hJ
  obtain ⟨he, hb⟩ := hN
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := HasRingHomProperty.Spec_iff.mpr he
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hP := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_psi φ I hb)
  rw [Spec.map_id] at hP
  refine hE hA1 q (Spec.map (CommRingCat.ofHom φ)) (Spec.map (CommRingCat.ofHom (psi φ I hb)))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) hP (off B (I.map φ)) (off A I) ?_ (Cl.off_map φ I)
  change (PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _
  congr 1
  have hr := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker] at hr
  rw [← hr]; rfl

end LateralTheory.CohomologicalPurity.NbPf
end
end
