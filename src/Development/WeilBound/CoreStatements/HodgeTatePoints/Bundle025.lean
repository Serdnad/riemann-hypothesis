module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenOnChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteOpenHopfOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Ma

open ChCoh

theorem coh_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∀ c, x c ≠ 0 → ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range b) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL c hc
  obtain ⟨n, b, h⟩ := finite_gen (A := chRing o x c) (E := E) ((chRing o x c).val : chRing o x c →+* Ω)
    (Pt := {p : Cpt M.ξ // InChart M.ξ x c p}) (fun q => regAt M.ξ q.1)
    (fun _ _ => rfl)
    (fun q a => (regat_loc o Ω κ x M c q.1 q.2).1 _ a.2)
    (fun q a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M c q.1 q.2).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩)
    (fun P hP => by
      obtain ⟨p, ⟨hp, hu⟩, -⟩ := prime_pt o Ω κ x M c hc P hP
      exact ⟨⟨p, hp⟩, hu⟩)
    (fun q => (reg_local M.X Ω M.ξ).1 q.1)
    (fun q => L q.1)
    (fun p => by
      obtain ⟨U, hU, n, b, hb⟩ := hL p.1 trivial
      obtain ⟨f, hf, hfu, hfU⟩ := basic o Ω κ x M c p.1 U p.2 hU
      exact ⟨⟨f, hf⟩, n, b, hfu, fun q hq => hb q.1 trivial (hfU q.1 q.2 hq)⟩)
  exact ⟨n, b, fun p hp => h ⟨p, hp⟩⟩

section

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
  (M : PModel o x) {E : Type} [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E)

theorem twist_mem {c j : κ} {t : Set E}
    (ht : ∀ p : Cpt M.ξ, InChart M.ξ x j p → L p = Submodule.span (regAt M.ξ p) t) {e : E}
    (he : ∀ p : Cpt M.ξ, InChart M.ξ x c p → e ∈ L p) :
    ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x j p → (x c / x j) ^ m • e ∈ L p := by
  by_cases hj : x j = 0
  · exact ⟨0, fun p hp => (hp.1 hj).elim⟩
  let ι : chRing o x j →+* Ω := (chRing o x j).val
  have hsm : ∀ (a : chRing o x j) (e : E), a • e = ι a • e := fun _ _ => rfl
  let f : chRing o x j := ⟨x c / x j, Algebra.subset_adjoin ⟨c, rfl⟩⟩
  have hrad : f ∈ (satIdeal (Submodule.span (chRing o x j) t) 1 e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, ⟨hq, hu⟩, -⟩ := prime_pt o Ω κ x M j hj P hP
    have hf : unitAt M.ξ q (x c / x j) := not_not.1 fun h => hn ((hu f).2 h)
    have hc : x c ≠ 0 := fun h => hf.1 (by rw [h, zero_div])
    have hqc : InChart M.ξ x c q := ⟨hc, fun k => by
      have : x k / x c = x k / x j * (x c / x j)⁻¹ := by field_simp
      rw [this]
      exact mul_mem (hq.2 k) hf.2.2⟩
    have hmem : e ∈ Submodule.span (regAt M.ξ q) t := ht q hq ▸ he q hqc
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (S := regAt M.ξ q) (fun a ha => by
      obtain ⟨u, hu, v, hv, hvu, e⟩ := ((regat_loc o Ω κ x M j q hq).2 a).1 ha
      exact ⟨⟨u, hu⟩, ⟨v, hv⟩, hvu, e⟩) t hmem
    exact (hu v).1 (hJP ⟨0, by simpa using hve⟩) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hq => ?_⟩
  rw [ht q hq]
  have h1 := mem_of_mem_spanA ι hsm (S := regAt M.ξ q)
    (fun a => (regat_loc o Ω κ x M j q hq).1 _ a.2) hk
  rw [hsm, one_pow, one_mul, map_pow] at h1
  exact h1

end

theorem serre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) := by
  intro o _ Ω _ _ κ _ x M E _ _ L hL
  have h1 : ∀ c, ∃ (n : ℕ) (b : Fin n → E), ∀ p : Cpt M.ξ, InChart M.ξ x c p →
      L p = Submodule.span (regAt M.ξ p) (Set.range b) := fun c => by
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun p hp => (hp.1 hc).elim⟩
    · exact coh_chart o Ω κ x M E L hL c hc
  choose n b hb using h1
  have h2 : ∀ s : (Σ c, Fin (n c)) × κ, ∃ m : ℕ, ∀ p : Cpt M.ξ, InChart M.ξ x s.2 p →
      (x s.1.1 / x s.2) ^ m • b s.1.1 s.1.2 ∈ L p := fun s =>
    twist_mem M L (hb s.2) fun p hp => by
      rw [hb _ p hp]
      exact Submodule.subset_span ⟨_, rfl⟩
  choose m hm using h2
  obtain ⟨d, hd⟩ := (Set.finite_range m).bddAbove
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (n c))
  refine ⟨d, N, fun k => x (e.symm k).1 ^ d • b (e.symm k).1 (e.symm k).2, fun j p hp => ?_⟩
  apply le_antisymm
  · rw [hb j p hp]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    refine ⟨e ⟨j, k⟩, ?_⟩
    dsimp only
    rw [e.symm_apply_apply, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hp.1), one_smul]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    set s := e.symm k
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (hd ⟨(s, j), rfl⟩ : m (s, j) ≤ d)
    have h3 := (L p).smul_mem (⟨(x s.1 / x j) ^ r, pow_mem (hp.2 _) _⟩ : regAt M.ξ p) (hm (s, j) p hp)
    have h4 : (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 =
        (x s.1 / x j) ^ r • (x s.1 / x j) ^ m (s, j) • b s.1 s.2 := by
      rw [smul_smul, smul_smul, ← pow_add, add_comm r, ← hr, div_pow, div_eq_inv_mul]
    change (x j ^ d)⁻¹ • x s.1 ^ d • b s.1 s.2 ∈ L p
    rw [h4]
    exact h3

end PositivityTheory.HtPt.Ma
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT
  GlobalTheory.CompanionTheory.Ar.BT.SubOrder PositivityTheory.HtPt.Twhopf

noncomputable section

namespace PositivityTheory.HtPt.Gi

section Pts

variable {Z : Scheme.{0}} {W : Over Z} {U : W.left.Opens} (hU : IsAffineOpen U)

abbrev affOver : Over Z := Over.mk (hU.fromSpec ≫ W.hom)

def taut : affOver hU ⟶ W := Over.homMk hU.fromSpec rfl

theorem taut_mem : ⊤ ≤ (taut hU).left ⁻¹ᵁ U := (top_le_iff_mem _ _).2 (fromSpec_mem hU)

theorem val_taut (h : ⊤ ≤ (taut hU).left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := Γ(W.left, U)) (taut hU).left U h s = s := by
  have e := spec_valHom_fromSpec (B := Γ(W.left, U)) (taut hU).left hU h
  have e2 : Spec.map (CommRingCat.ofHom (valHom (B := Γ(W.left, U)) (taut hU).left U h)) = Spec.map (𝟙 _) := by
    rw [← cancel_mono hU.fromSpec, e, Spec.map_id, Category.id_comp]
    rfl
  exact congrArg (fun f => f.hom s) (Spec.map_injective e2)

def fac {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W) (h : ⊤ ≤ z.left ⁻¹ᵁ U) :
    Over.mk f ⟶ affOver hU :=
  Over.homMk (Spec.map (CommRingCat.ofHom (valHom (B := B) z.left U h))) (by
    have e := spec_valHom_fromSpec (B := B) z.left hU h
    change _ ≫ hU.fromSpec ≫ W.hom = f
    rw [← Category.assoc]
    exact (congrArg (· ≫ W.hom) e).trans (Over.w z))

theorem fac_taut {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W)
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) : fac hU z h ≫ taut hU = z :=
  Over.OverMorphism.ext (spec_valHom_fromSpec (B := B) z.left hU h)


include hU in
theorem val_comp {B C : Type} [CommRing B] [CommRing C] {f : Spec (CommRingCat.of B) ⟶ Z}
    {g : Spec (CommRingCat.of C) ⟶ Z} (q : Over.mk g ⟶ Over.mk f) (φ : B →+* C)
    (hq : q.left = Spec.map (CommRingCat.ofHom φ)) (a : Over.mk f ⟶ W) (h : ⊤ ≤ a.left ⁻¹ᵁ U)
    (b : Over.mk g ⟶ W) (hb : b = q ≫ a) (h' : ⊤ ≤ b.left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := C) b.left U h' s = φ (valHom (B := B) a.left U h s) := by
  have e : b.left = Spec.map (CommRingCat.ofHom φ) ≫ a.left := by rw [hb, Over.comp_left, hq]
  exact (DFunLike.congr_fun (valHom_congr (B := C) e U h' (e ▸ h')) s).trans
    (valHom_comp (B := B) a.left hU h φ _ s)

theorem comp_mem {Y Y' : Over Z} (q : Y' ⟶ Y) (a : Y ⟶ W) (h : ⊤ ≤ a.left ⁻¹ᵁ U) (b : Y' ⟶ W) (hb : b = q ≫ a) :
    ⊤ ≤ b.left ⁻¹ᵁ U := by
  subst hb
  exact fun z _ => h (Set.mem_univ (q.left z))

theorem val_fac {W' : Over Z} {U' : W'.left.Opens} (hU' : IsAffineOpen U') (k : affOver hU ⟶ W')
    (hk : ⊤ ≤ k.left ⁻¹ᵁ U') {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W)
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) (b : Over.mk f ⟶ W') (hb : b = fac hU z h ≫ k) :
    ∃ h', ∀ s, valHom (B := B) b.left U' h' s =
      valHom (B := B) z.left U h (valHom (B := Γ(W.left, U)) k.left U' hk s) :=
  ⟨comp_mem _ k hk b hb, fun s => val_comp (B := Γ(W.left, U)) hU' (fac hU z h) _ rfl k hk b hb _ s⟩


include hU in
theorem pt_ext {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (a b : Over.mk f ⟶ W)
    (ha : ⊤ ≤ a.left ⁻¹ᵁ U) (hb : ⊤ ≤ b.left ⁻¹ᵁ U)
    (h : ∀ s, valHom (B := B) a.left U ha s = valHom (B := B) b.left U hb s) : a = b := by
  apply Over.OverMorphism.ext
  have e1 := spec_valHom_fromSpec (B := B) a.left hU ha
  have e2 := spec_valHom_fromSpec (B := B) b.left hU hb
  rw [RingHom.ext h] at e1
  exact e1.symm.trans e2

theorem val_congr {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} {a b : Over.mk f ⟶ W} (e : a = b)
    (ha : ⊤ ≤ a.left ⁻¹ᵁ U) (hb : ⊤ ≤ b.left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := B) a.left U ha s = valHom (B := B) b.left U hb s := by
  subst e; rfl

theorem affOver_finite (h : IsFinite (U.ι ≫ W.hom)) : IsFinite (affOver hU).hom := by
  change IsFinite (hU.fromSpec ≫ W.hom)
  rw [← hU.isoSpec_inv_ι, Category.assoc]
  infer_instance

end Pts

variable {R : Type} [CommRing R] [IsLocalRing R] {W W' : Over (Spec (CommRingCat.of R))} [GrpObj W']



theorem core {N : ℕ} (j : W ⟶ W') (hinj : ∀ (Y) (y y' : Y ⟶ W), y ≫ j = y' ≫ j → y = y')
    (hker : ∀ (Y) (z : Y ⟶ W'), z ^ N = 1 ↔ ∃ y, y ≫ j = z) (U : W.left.Opens) (U' : W'.left.Opens)
    (hF : IsFinite (U.ι ≫ W.hom)) (hF' : IsFinite (U'.ι ≫ W'.hom))
    (hU : ∀ x : W.left, W.hom x = IsLocalRing.closedPoint R → x ∈ U)
    (hU' : ∀ x : W'.left, W'.hom x = IsLocalRing.closedPoint R → x ∈ U') :
    ∃ r : Γ(W'.left, U') →+* Γ(W.left, U), Function.Surjective r ∧
      (∀ (z : genPt R ⟶ W) h, ∃ h', ∀ s, valAt z.left U h (r s) = valAt (z ≫ j).left U' h' s) ∧
      ∀ I : Ideal Γ(W'.left, U'), (∀ s c, (∀ (z : genPt R ⟶ W') h, ∃ hN h1, valAt z.left U' h c =
        valAt (z ^ N).left U' hN s - valAt (1 : genPt R ⟶ W').left U' h1 s) → c ∈ I) → RingHom.ker r ≤ I := by
  have hA : IsAffineOpen U := isAffine_of_isAffineHom (U.ι ≫ W.hom)
  have hA' : IsAffineOpen U' := isAffine_of_isAffineHom (U'.ι ≫ W'.hom)
  have hY := affOver_finite hA hF
  have hY' := affOver_finite hA' hF'
  have m1 : ∀ a : affOver hA ⟶ W', ⊤ ≤ a.left ⁻¹ᵁ U' := fun a z _ => mem_of_finite U' hU' _ hY a z
  have m2 : ∀ a : affOver hA' ⟶ W', ⊤ ≤ a.left ⁻¹ᵁ U' := fun a z _ => mem_of_finite U' hU' _ hY' a z
  let r : Γ(W'.left, U') →+* Γ(W.left, U) := valHom (B := Γ(W.left, U)) (taut hA ≫ j).left U' (m1 _)
  have hr : ∀ {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ _} (z : Over.mk f ⟶ W) h,
      ∃ h', ∀ s, valHom (B := B) z.left U h (r s) = valHom (B := B) (z ≫ j).left U' h' s := by
    intro B _ f z h
    have e : z ≫ j = fac hA z h ≫ taut hA ≫ j := by rw [← Category.assoc, fac_taut]
    obtain ⟨h', e'⟩ := val_fac hA hA' _ (m1 _) z h _ e
    exact ⟨h', fun s => (e' s).symm⟩
  let δ : Γ(W'.left, U') → Γ(W'.left, U') := fun s =>
    valHom (B := Γ(W'.left, U')) (taut hA' ^ N).left U' (m2 _) s -
      valHom (B := Γ(W'.left, U')) (1 : affOver hA' ⟶ W').left U' (m2 _) s
  have hδ : ∀ {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ _} (z : Over.mk f ⟶ W') h,
      ∃ hN h1, ∀ s, valHom (B := B) z.left U' h (δ s) =
        valHom (B := B) (z ^ N).left U' hN s - valHom (B := B) (1 : Over.mk f ⟶ W').left U' h1 s := by
    intro B _ f z h
    have e : z ^ N = fac hA' z h ≫ taut hA' ^ N := by rw [MonObj.comp_pow, fac_taut]
    have e1 : (1 : Over.mk f ⟶ W') = fac hA' z h ≫ 1 := (MonObj.comp_one _).symm
    obtain ⟨hN, eN⟩ := val_fac hA' hA' _ (m2 _) z h _ e
    obtain ⟨h1, e1⟩ := val_fac hA' hA' _ (m2 _) z h _ e1
    exact ⟨hN, h1, fun s => (map_sub _ _ _).trans (congrArg₂ (· - ·) (eN s).symm (e1 s).symm)⟩
  let I₀ : Ideal Γ(W'.left, U') := Ideal.span (Set.range δ)
  let π := Ideal.Quotient.mk I₀
  let f₀ := Spec.map (CommRingCat.ofHom π) ≫ hA'.fromSpec ≫ W'.hom
  let q : Over.mk f₀ ⟶ affOver hA' := Over.homMk (Spec.map (CommRingCat.ofHom π)) rfl
  have hf₀ : IsFinite (Over.mk f₀).hom := by
    have : IsFinite (Spec.map (CommRingCat.ofHom π)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective π Ideal.Quotient.mk_surjective)
    have : IsFinite (hA'.fromSpec ≫ W'.hom) := hY'
    exact inferInstanceAs (IsFinite (Spec.map (CommRingCat.ofHom π) ≫ hA'.fromSpec ≫ W'.hom))
  have hqm := comp_mem q _ (taut_mem hA') _ rfl
  have hq : ∀ s, valHom (B := _ ⧸ I₀) (q ≫ taut hA').left U' hqm s = π s := fun s => by
    rw [val_comp (B := Γ(W'.left, U')) hA' q π rfl _ (taut_mem hA') _ rfl _ s, val_taut]
  have hqN : (q ≫ taut hA') ^ N = 1 := by
    obtain ⟨hN, h1, e⟩ := hδ (q ≫ taut hA') hqm
    refine pt_ext hA' _ _ hN h1 fun s => ?_
    rw [← sub_eq_zero, ← e, hq]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
  obtain ⟨y, hy⟩ := (hker _ _).1 hqN
  have hym : ⊤ ≤ y.left ⁻¹ᵁ U := fun z _ => mem_of_finite U hU _ hf₀ y z
  have hyr : ∀ s, valHom (B := _ ⧸ I₀) y.left U hym (r s) = π s := fun s => by
    obtain ⟨h', e⟩ := hr (B := _ ⧸ I₀) (f := f₀) y hym
    exact (e s).trans ((val_congr hy h' hqm s).trans (hq s))
  refine ⟨r, fun s => ?_, fun z h => hr z h, fun I hI s hs => ?_⟩
  · have h0 : ∀ a ∈ I₀, r a = 0 := by
      intro a ha
      refine (show I₀ ≤ RingHom.ker r from Ideal.span_le.2 ?_) ha
      rintro _ ⟨t, rfl⟩
      obtain ⟨hN, h1, e⟩ := hδ (B := Γ(W.left, U)) (taut hA ≫ j) (m1 _)
      have e1 : (taut hA ≫ j) ^ N = 1 := (hker _ _).2 ⟨_, rfl⟩
      refine (e t).trans (sub_eq_zero.2 ?_)
      exact val_congr (B := Γ(W.left, U)) e1 hN h1 t
    let rb := Ideal.Quotient.lift I₀ r h0
    have e0 : Spec.map (CommRingCat.ofHom rb) ≫ Spec.map (CommRingCat.ofHom π) = Spec.map (CommRingCat.ofHom r) := by
      rw [← Spec.map_comp]
      rfl
    let v : affOver hA ⟶ Over.mk f₀ := Over.homMk (Spec.map (CommRingCat.ofHom rb)) (by
      change _ ≫ Spec.map (CommRingCat.ofHom π) ≫ _ = _
      rw [← Category.assoc, e0]
      exact Over.w (fac (B := Γ(W.left, U)) hA' (taut hA ≫ j) (m1 _)))
    have e1 : v ≫ q = fac (B := Γ(W.left, U)) hA' (taut hA ≫ j) (m1 _) := Over.OverMorphism.ext e0
    have e2 : taut hA = v ≫ y := hinj _ _ _ (by
      rw [Category.assoc, hy, ← Category.assoc, e1, fac_taut])
    have e3 := val_comp (C := Γ(W.left, U)) hA v rb rfl y hym _ e2 (taut_mem hA) s
    rw [val_taut] at e3
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (valHom (B := _ ⧸ I₀) y.left U hym s)
    exact ⟨s', by rw [e3, ← hs']; rfl⟩
  · have h1 : s ∈ I₀ := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := hyr s
      rw [(RingHom.mem_ker).1 hs, map_zero] at this
      exact this.symm
    refine (show I₀ ≤ I from Ideal.span_le.2 ?_) h1
    rintro _ ⟨t, rfl⟩
    refine hI t _ fun z h => ?_
    obtain ⟨hN, h1, e⟩ := hδ z h
    exact ⟨hN, h1, e t⟩

end PositivityTheory.HtPt.Gi
end
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Mh

open scoped CategoryTheory.Obj

section Bridge
variable {S' S : Scheme.{0}} (x : S' ⟶ S) (G : Over S)

def toPull {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) : Y ⟶ (Over.pullback x).obj G :=
  Over.homMk (pullback.lift g.left Y.hom (by simpa using Over.w g)) (pullback.lift_snd _ _ _)

theorem toPull_fst {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    (toPull x G g).left ≫ pullback.fst G.hom x = g.left := pullback.lift_fst _ _ _

variable {x G} in
theorem hom_ext_pull {Y : Over S'} {y z : Y ⟶ (Over.pullback x).obj G}
    (h : y.left ≫ pullback.fst G.hom x = z.left ≫ pullback.fst G.hom x) : y = z := by
  ext
  refine pullback.hom_ext h ?_
  have h1 := Over.w y
  have h2 := Over.w z
  simp only [Over.pullback_obj_hom] at h1 h2
  rw [h1, h2]

theorem toPull_eq {Y : Over S'} (g : Over.mk (Y.hom ≫ x) ⟶ G) :
    toPull x G g = toPull x _ (𝟙 (Over.mk (Y.hom ≫ x))) ≫ (Over.pullback x).map g := by
  apply hom_ext_pull
  have h1 : ((Over.pullback x).map g).left ≫ pullback.fst G.hom x = pullback.fst _ x ≫ g.left :=
    pullback.lift_fst _ _ _
  have h2 := toPull_fst x _ (𝟙 (Over.mk (Y.hom ≫ x)))
  rw [toPull_fst, Over.comp_left, Category.assoc, h1, ← Category.assoc, h2]
  simp

def toPullHom [GrpObj G] (Y : Over S') : (Over.mk (Y.hom ≫ x) ⟶ G) →* (Y ⟶ (Over.pullback x).obj G) where
  toFun := toPull x G
  map_one' := by
    rw [toPull_eq, Functor.map_one, MonObj.comp_one]
  map_mul' g h := by
    rw [toPull_eq, toPull_eq x G g, toPull_eq x G h, Functor.map_mul, MonObj.comp_mul]

def ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : Over.mk (Y.hom ≫ x) ⟶ G :=
  Over.homMk (y.left ≫ pullback.fst G.hom x) (by
    have h1 := Over.w y
    simp only [Over.pullback_obj_hom] at h1
    simp [pullback.condition, reassoc_of% h1])

theorem toPull_ofPull {Y : Over S'} (y : Y ⟶ (Over.pullback x).obj G) : toPull x G (ofPull x G y) = y := by
  apply hom_ext_pull
  rw [toPull_fst]
  rfl

end Bridge

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torFst (S : Scheme.{0}) (X : Type) [AddCommGroup X] :
    (splitTorus S X).left ⟶ Spec (CommRingCat.of (AddMonoidAlgebra ZU.{0} X)) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

def chi {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) : Multiplicative X →* Γ(Y, ⊤) :=
  (pb (g ≫ torFst S X)).toMonoidHom.comp (AddMonoidAlgebra.of ZU.{0} X)

theorem chi_apply {Y : Scheme.{0}} (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi g x = pb (g ≫ torFst S X) (AddMonoidAlgebra.single x.toAdd 1) := rfl

theorem chi_comp {Y Y' : Scheme.{0}} (f : Y' ⟶ Y) (g : Y ⟶ (splitTorus S X).left) (x : Multiplicative X) :
    chi (f ≫ g) x = f.appTop (chi g x) := by
  rw [chi_apply, chi_apply, Category.assoc, pb_comp]

theorem chi_ext {Y : Scheme.{0}} {g h : Y ⟶ (splitTorus S X).left}
    (w : g ≫ (splitTorus S X).hom = h ≫ (splitTorus S X).hom) (e : ∀ x, chi g x = chi h x) : g = h := by
  refine pullback.hom_ext (f := (splitTorusAff ZU X).hom) (g := toZ S) ?_ w
  refine pb_ext (j := g ≫ torFst S X) (j' := h ≫ torFst S X) (RingHom.congr_fun ?_)
  refine AddMonoidAlgebra.ringHom_ext (fun r => ?_) fun m => e (Multiplicative.ofAdd m)
  have e1 : ∀ k : Y ⟶ (splitTorus S X).left, pb (k ≫ torFst S X) (AddMonoidAlgebra.single 0 r) = pb (toZ Y) r := by
    intro k
    refine (pb_spec (k ≫ torFst S X) (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)) r).symm.trans ?_
    congr 2
    exact specULiftZIsTerminal.hom_ext _ _
  rw [e1, e1]

theorem exists_chi (Y : Over S) (c : Multiplicative X →* Γ(Y.left, ⊤)) :
    ∃ g : Y ⟶ splitTorus S X, ∀ x, chi g.left x = c x := by
  obtain ⟨j, hj⟩ := exists_pb (AddMonoidAlgebra.liftNCRingHom (k := ZU.{0}) (pb (toZ Y.left)) c
    fun _ _ => Commute.all _ _)
  refine ⟨Over.homMk (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) (pullback.lift_snd _ _ _), fun x => ?_⟩
  have e : (pullback.lift (f := (splitTorusAff ZU X).hom) (g := toZ S) j Y.hom
    (specULiftZIsTerminal.hom_ext _ _)) ≫ torFst S X = j := pullback.lift_fst _ _ _
  refine (congrArg (fun k => pb k (AddMonoidAlgebra.single x.toAdd 1)) e).trans ?_
  rw [hj, AddMonoidAlgebra.liftNCRingHom_single, map_one, _root_.one_mul]
  rfl

theorem pb_mul_aff {Y : Over (Spec ZU.{0})} (g h : Y ⟶ splitTorusAff ZU X) (x : X) :
    pb (A := AddMonoidAlgebra ZU.{0} X) (g * h).left (AddMonoidAlgebra.single x 1) =
      pb (A := AddMonoidAlgebra ZU.{0} X) g.left (AddMonoidAlgebra.single x 1) *
        pb (A := AddMonoidAlgebra ZU.{0} X) h.left (AddMonoidAlgebra.single x 1) := by
  let A := AddMonoidAlgebra ZU.{0} X
  let q : Y.left ⟶ Spec (CommRingCat.of (A ⊗[ZU.{0}] A)) := (lift g h).left ≫ (pullbackSpecIso ZU.{0} A A).hom
  have e0 : (g * h).left = q ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom ZU.{0} A : A →+* A ⊗[ZU.{0}] A)) := rfl
  have e1 : q ≫ Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) = g.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_fst ZU.{0} A A)).trans
      (congrArg (·.left) (lift_fst g h)))
  have e2 : q ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom Algebra.TensorProduct.includeRight)) = h.left :=
    (Category.assoc _ _ _).trans ((congrArg ((lift g h).left ≫ ·) (pullbackSpecIso_hom_snd ZU.{0} A A)).trans
      (congrArg (·.left) (lift_snd g h)))
  rw [e0, ← e1, ← e2, pb_spec, pb_spec, pb_spec, ← map_mul]
  congr 1
  simp [A, AddMonoidAlgebra.comul_single]

theorem chi_mul {Y : Over S} (g h : Y ⟶ splitTorus S X) (x : Multiplicative X) :
    chi (g * h).left x = chi g.left x * chi h.left x := by
  let g' := ofPull (toZ S) (splitTorusAff ZU X) g
  let h' := ofPull (toZ S) (splitTorusAff ZU X) h
  have e : g * h = toPull (toZ S) (splitTorusAff ZU X) (g' * h') :=
    ((map_mul (toPullHom (toZ S) (splitTorusAff ZU X) Y) g' h').trans
      (congrArg₂ (· * ·) (toPull_ofPull _ _ g) (toPull_ofPull _ _ h))).symm
  have e' : (g * h).left ≫ torFst S X = (g' * h').left := by
    rw [e]
    exact toPull_fst _ _ _
  rw [chi_apply, e']
  exact pb_mul_aff g' h' x.toAdd

theorem chi_one (Y : Over S) (x : Multiplicative X) : chi (1 : Y ⟶ splitTorus S X).left x = 1 := by
  have h := chi_mul (1 : Y ⟶ splitTorus S X) 1 x
  rw [_root_.mul_one] at h
  have hu : IsUnit (chi (1 : Y ⟶ splitTorus S X).left x) := (Group.isUnit x).map _
  exact (hu.mul_eq_left.1 h.symm)

theorem chi_pow {Y : Over S} (g : Y ⟶ splitTorus S X) (x : Multiplicative X) (n : ℕ) :
    chi (g ^ n).left x = chi g.left x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, chi_one]
  | succ n ih => rw [pow_succ, pow_succ, chi_mul, ih]

theorem pow_eq_one_iff_chi {Y : Over S} (g : Y ⟶ splitTorus S X) (n : ℕ) :
    g ^ n = 1 ↔ ∀ x, chi g.left x ^ n = 1 := by
  refine ⟨fun h x => by rw [← chi_pow, h, chi_one], fun h => Over.OverMorphism.ext (chi_ext ?_ fun x => ?_)⟩
  · exact (Over.w _).trans (Over.w _).symm
  · rw [chi_pow, h, chi_one]

end PositivityTheory.HtPt.Mh
end
end
