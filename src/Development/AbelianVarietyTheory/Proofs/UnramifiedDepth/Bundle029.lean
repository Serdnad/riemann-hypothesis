module

public import ReciprocityTheory.DualLattices.Bundle024
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.Bundle021
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

section

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p}
  {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe]
  {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)

end


open TensorProduct IsLocalRing Matrix in
theorem _root_.GlobalTheory.evImg_isLat_subring :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement D) := by
  intro R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvLatStatement
  intro C _ _ hdom hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => by
        have h := congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 o) (hspec t).1
        exact h }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  haveI : ∀ i, Module.Free Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).1
  haveI : ∀ i, Module.Finite Tw.O.carrier (D.fin.AAx i).carrier := fun i => (D.fin.free i).2
  haveI := hdom
  have hrank : Module.finrank Tw.O.carrier (∀ i, (D.fin.AAx i).carrier) = Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [Module.finrank_pi_fintype, ← Nat.card_eq_fintype_card]
    refine Eq.trans ?_ (D.fin.rank.trans (Nat.card_congr (Equiv.ofBijective _ D.L.τ_basis)).symm)
    rfl
  let b0 := Module.Free.chooseBasis Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex Tw.O.carrier (∀ i, (D.fin.AAx i).carrier)) =
      Fintype.card (_root_.ReciprocityTheory.PGsh.Up.Nb p g) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hrank]
  let b := b0.reindex (Fintype.equivOfCardEq hcard)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.PGsh.L2.IsLat
    refine ⟨Matrix.of fun x j => f (b j) x, ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      have hdet : (Matrix.of fun x j => f (b j) x).det =
          algebraMap Tw.O.carrier C (Matrix.of fun x j => Ψ (b j) x).det := by
        rw [RingHom.map_det]; rfl
      rw [hdet]
      intro h0
      rw [← map_zero (algebraMap Tw.O.carrier C)] at h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (hinj h0)
      apply hv0
      have hsum : Ψ (∑ j, v j • b j) = 0 := by
        rw [← hv]
        funext x

        simp [Matrix.mulVec, dotProduct, map_sum, map_smul, mul_comm]
      have h1 : ∑ j, v j • b j = 0 := hinjΨ (by rw [hsum, map_zero])
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent v h1 j
    · rw [himg]
      change _ = Submodule.span _ (Set.range (f ∘ b))
      rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
  · rw [himg]
    rintro _ ⟨F, rfl⟩
    exact fun x => ⟨_, (hf F x).symm⟩
  · rw [himg]
    exact ⟨1, by funext x; simp only [hf, Pi.one_apply, map_one]⟩
  · rw [himg]
    rintro _ _ ⟨F, rfl⟩ ⟨G, rfl⟩
    exact ⟨F * G, by funext x; simp only [hf, Pi.mul_apply, map_mul]⟩

end GlobalTheory
end
end

section

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

namespace BtAssembly

variable {R₀ : Type} [CommRing R₀]

private lemma chi_congr {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) {x y : B.G R} (hx : B.map ρ x = 0) (hy : B.map ρ y = 0)
    (h : x = y) : ch.χ ρ hρ ⟨x, hx⟩ = ch.χ ρ hρ ⟨y, hy⟩ := by
  subst h; rfl

private lemma chi_zero {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (h0 : B.map ρ 0 = 0) (k : Fin g) :
    ((ch.χ ρ hρ ⟨0, h0⟩ k : maximalIdeal (R : Type)) : (R : Type)) = 0 := by
  have hsq : (LHom.id R).SqZero := by
    refine ⟨fun a => ⟨a, rfl⟩, ?_⟩
    have : RingHom.ker (LHom.id R).1 = ⊥ := by
      ext a; simp [RingHom.mem_ker, LHom.id]
    rw [this]; simp
  have h := ch.χ_tg ρ hρ (LHom.id R) hsq ρ rfl 0 0 k
  rw [chi_congr ch ρ hρ _ h0 (by simp)] at h
  simpa using h

private lemma chi_nsmul {B : BX R₀} {K : LAlg R₀} {g : ℕ} (ch : FormalChartAtZero B K g) {R : LAlg R₀}
    (ρ : LHom R K) (hρ : IsNilOver ρ) (x : B.G R) (hx : B.map ρ x = 0) (n : ℕ)
    (hn : B.map ρ (n • x) = 0) :
    (fun k => ((ch.χ ρ hρ ⟨n • x, hn⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      nsmulF ch.F (fun k => ((ch.χ ρ hρ ⟨x, hx⟩ k : maximalIdeal (R : Type)) : (R : Type))) n := by
  induction n with
  | zero =>
    funext k
    rw [chi_congr ch ρ hρ hn (map_zero _) (zero_nsmul x), chi_zero]
    rfl
  | succ n ih =>
    have hn' : B.map ρ (n • x) = 0 := by rw [map_nsmul, hx, nsmul_zero]
    have h := ch.χ_add ρ hρ ⟨n • x, hn'⟩ ⟨x, hx⟩
    rw [ih hn'] at h
    rw [chi_congr ch ρ hρ hn (map_add_ker B ρ ⟨n • x, hn'⟩ ⟨x, hx⟩) (succ_nsmul x n)]
    exact h

private lemma nil_of_mem {R K : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ)
    (hK : maximalIdeal (K : Type) = ⊥) (a : maximalIdeal (R : Type)) :
    IsNilpotent (a : (R : Type)) := by
  apply hρ.2
  rw [RingHom.mem_ker]
  have : ρ.1 a ∈ maximalIdeal (K : Type) := fun hu => a.2 (ρ.2.map_nonunit _ hu)
  rw [hK] at this
  exact this

private lemma exists_pow_zero {S : Type} [CommRing S] {g : ℕ} (Y : Fin g → S)
    (h : ∀ l, IsNilpotent (Y l)) : ∃ N : ℕ, ∀ l, Y l ^ N = 0 := by
  choose n hn using h
  refine ⟨∑ l, n l, fun l => pow_eq_zero_of_le ?_ (hn l)⟩
  exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

private lemma comp_app {R S T : LAlg R₀} (f : LHom R S) (f' : LHom S T) (e : LHom R T)
    (h : f'.comp f = e) (a : (R : Type)) : f'.1 (f.1 a) = e.1 a := by
  subst h; rfl

end BtAssembly


open BtAssembly in
theorem evBt_of_tangent_of_series :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ t : TT p g, ∃ t' : B.G D.wd.W,
    B.map D.wd.πW t' = B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) ∧
    ∃ h : B.map D.wd.ρW (p • t') = 0, ∀ k : Fin g, ∃ w : (D.wd.W : Type),
      D.wd.πW.1 w = (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) ∧
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨p • t', h⟩ k : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) = p * (D.wd.b : (D.wd.W : Type)) * w) →
  (∀ {R₀ : Type} [CommRing R₀] (p : ℕ) [Fact p.Prime] {g : ℕ} {B : BX R₀} {K : LAlg R₀} (ch : FormalChartAtZero B K g) (W : Type) [CommRing W] [Algebra R₀ W] (c : Fin g → W),
    (∀ i, IsNilpotent (c i)) → ∀ N : ℕ, ∃ Γ : Fin g → MvPolynomial (Fin g) W,
      (∀ k m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff (Γ k) m ∈ Ideal.span {(p : W)}) ∧
      ∀ y : Fin g → W, (∀ i, y i ^ N = 0) → fAdd ch.F c (nsmulF ch.F y p) = fun k => MvPolynomial.eval y (Γ k)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀} (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvBtStatement D) := by
  intro hTAN hGAM hLAM hWF R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  obtain ⟨hK, hρ1, hL⟩ := hLAM D (Fin.pos k)
  have key : ∀ i : D.fin.ι, ∃ F : (D.fin.AAx i : Type), ∀ φ : LHom (D.fin.AAx i) Tw.O,
      φ.comp (D.fin.sO i) = LHom.id Tw.O → ∀ t : TT p g,
      B.map φ (D.fin.y i) = ptOf B D.L.τ (red p g t) →
      (Tw.q 0).1 ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) = (Tw.q 0).1 (φ.1 F) := by
    intro i
    obtain ⟨Λ, μ, j, ρΛ, hΛ, hμ, hj, -, hψ⟩ := hL i
    obtain ⟨x, hx⟩ := D.sm.onto (B.map ρΛ (B.map μ (D.fin.y i)))
    have hc : B.map D.wd.ρW (p • x) = 0 := by
      rw [map_nsmul, hx, ← map_nsmul, ← map_nsmul, D.fin.y_p, map_zero, map_zero]
    have hz : B.map ρΛ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) = 0 := by
      rw [map_sub, ← B.map_comp j ρΛ, hj, ← B.map_comp D.wd.πW, D.wd.ρW_eq, hx, sub_self]
    obtain ⟨N, hN⟩ := exists_pow_zero
      (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)))
      (fun l => nil_of_mem ρΛ hΛ hK _)
    obtain ⟨Γ, hΓ, hΓe⟩ := hGAM p D.ch (D.wd.W : Type)
      (fun l => ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hc⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)))
      (fun l => nil_of_mem D.wd.ρW D.sm.nil hK _) (N * 2)
    obtain ⟨Q, hQ⟩ := hWF D.wd g (Γ k) (hΓ k)
    obtain ⟨F, hF⟩ := hμ (j.1 (D.wd.πW.1 ((D.wd.b⁻¹ : (D.wd.W : Type)ˣ) : (D.wd.W : Type))) *
      MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q)
    refine ⟨F, fun φ hφ t ht => ?_⟩
    obtain ⟨ψ, hψμ, hψj, hψρ⟩ := hψ φ hφ
    obtain ⟨t', ht', h, hw⟩ := hTAN D t
    obtain ⟨w, hw1, hw2⟩ := hw k
    have e1 : B.map D.wd.πW t' = B.map ψ (B.map μ (D.fin.y i)) := by
      rw [ht', ← ht, ← B.map_comp, ← B.map_comp, hψμ]
    have hu : B.map D.wd.ρW (t' - x) = 0 := by
      rw [map_sub, hx, ← D.wd.ρW_eq, B.map_comp, e1, ← B.map_comp ψ, hψρ, sub_self]
    have e2 : B.map D.wd.πW (t' - x) =
        B.map ψ (B.map μ (D.fin.y i) - B.map j (B.map D.wd.πW x)) := by
      rw [map_sub, map_sub, e1, ← B.map_comp j ψ, hψj, B.map_id]
    have e3 : ∀ l, D.wd.πW.1
        ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type)) =
        ψ.1 ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type)) := by
      intro l
      rw [← D.ch.χ_nat D.wd.ρW D.wd.ρ1 D.sm.nil hρ1 D.wd.πW D.wd.ρW_eq ⟨_, hu⟩ l,
        ← D.ch.χ_nat ρΛ D.wd.ρ1 hΛ hρ1 ψ hψρ ⟨_, hz⟩ l]
      rw [chi_congr D.ch D.wd.ρ1 hρ1 _ _ e2]
    have e4 : ∀ l, ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
        (D.wd.W : Type)) ^ (N * 2) = 0 := by
      intro l
      have : ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) :
          (D.wd.W : Type)) ^ N ∈ RingHom.ker D.wd.πW.1 := by
        rw [RingHom.mem_ker, map_pow, e3, ← map_pow, hN, map_zero]
      rw [D.wd.ker_πW, Ideal.mem_span_singleton'] at this
      obtain ⟨a, ha⟩ := this
      rw [pow_mul, ← ha, mul_pow, D.wd.p_sq, mul_zero]
    have hpu : B.map D.wd.ρW (p • (t' - x)) = 0 := by rw [map_nsmul, hu, nsmul_zero]
    have e5 := D.ch.χ_add D.wd.ρW D.sm.nil ⟨_, hc⟩ ⟨_, hpu⟩
    rw [chi_nsmul D.ch D.wd.ρW D.sm.nil _ hu p hpu, hΓe _ e4,
      chi_congr D.ch D.wd.ρW D.sm.nil _ h
        (show p • x + p • (t' - x) = p • t' by rw [← nsmul_add, add_sub_cancel])] at e5
    have e6 := congrFun e5 k
    rw [hw2] at e6
    obtain ⟨a, ha⟩ := D.wd.πW_surj (MvPolynomial.eval (fun l => D.wd.πW.1
      ((D.ch.χ D.wd.ρW D.sm.nil ⟨_, hu⟩ l : maximalIdeal (D.wd.W : Type)) : (D.wd.W : Type))) Q)
    have e7 := hQ _ (by
      rw [← e6, mul_assoc]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) a ha
    rw [← e6] at e7
    have e8 : D.wd.πW.1 ((D.wd.b : (D.wd.W : Type)) * w - a) = 0 := by
      rw [← D.wd.ann_p, mul_sub, ← mul_assoc, e7, sub_self]
    rw [map_sub, sub_eq_zero] at e8
    have e9 : ψ.1 (MvPolynomial.eval₂ (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q) =
        D.wd.πW.1 a := by
      rw [ha]
      have hid : (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type)).comp
          (j.1 : (Tw.R 0 : Type) →+* (Λ : Type)) = RingHom.id _ :=
        RingHom.ext fun b => comp_app j ψ _ hψj b
      have := MvPolynomial.eval₂_comp_left (ψ.1 : (Λ : Type) →+* (Tw.R 0 : Type))
        (j.1 : (Tw.R 0 : Type) →+* (Λ : Type))
        (fun l => ((D.ch.χ ρΛ hΛ ⟨_, hz⟩ l : maximalIdeal (Λ : Type)) : (Λ : Type))) Q
      rw [hid] at this
      refine this.trans ?_
      rw [MvPolynomial.eval₂_id]
      congr 2
      funext l
      exact (e3 l).symm
    have e10 : (Tw.q 0).1 (φ.1 F) = ψ.1 (μ.1 F) := (comp_app μ ψ _ hψμ F).symm
    rw [e10, hF, map_mul, e9, comp_app j ψ _ hψj, ← hw1, ← e8]
    change _ = D.wd.πW.1 _ * _
    rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  choose F hF using key
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  have hs := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  have h := hF (D.ptIdx (red p g t)) (D.ptMap (red p g t)) hs.1 t hs.2.1
  have hm : (D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hm
  obtain ⟨r, hr⟩ := hm
  refine ⟨r, ?_⟩
  rw [mul_comm, hr, map_sub]
  rfl

end GlobalTheory
end
end
