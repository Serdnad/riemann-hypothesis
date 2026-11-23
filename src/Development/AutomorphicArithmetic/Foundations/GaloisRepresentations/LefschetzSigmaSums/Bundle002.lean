module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle853
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open UpperTheory.Gal.LocalSmoothExtension

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open GlobalTheory.UPel.HT.MapComp

theorem UpperTheory.Gal.LocalSmoothExtension.mapEq_of :
    MapEq := by
  intro G R _ _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g m₂
  refine ⟨fun m₁ => ?_, fun m => ?_⟩
  · refine ⟨⟨m₁.φ ≫ m₂.φ, m₁.φ₂ ≫ m₂.φ₂, IsGrpPullback.comp m₁.cart m₂.cart,
      isSquare_comp m₁.sq m₂.sq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol
        (lbIso_pull_comp m₂.pol m₁.φ₂ rfl), fun y => ?_⟩, rfl⟩
    · rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
    · rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]
  · have hw : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by
      rw [Category.assoc]; exact m.cart.1.w
    let φ : o₁.A.left ⟶ o₂.A.left := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) hw
    have h₁ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
    have h₂ : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
    obtain ⟨φ₂, hsq⟩ := exists_isSquare h₂
    have h₃ : φ₂ ≫ m₂.φ₂ = m.φ₂ := by
      have := isSquare_comp hsq m₂.sq
      rw [h₁] at this
      exact isSquare_unique this m.sq
    have hc : IsGrpPullback o₁.A o₂.A f φ :=
      IsGrpPullback.cancel m₂.cart (by rw [h₁]; exact m.cart) h₂
    refine ⟨⟨φ, φ₂, hc, hsq, fun c => ?_,
      LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
        (lbIso_pull_comp m₂.pol φ₂ h₃.symm).symm, fun y => ?_⟩, h₁⟩
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.act, Category.assoc, m₂.act, ← Category.assoc, h₁]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, h₂, ← Category.assoc, Over.w]
    · apply m₂.cart.1.hom_ext
      · rw [Category.assoc, h₁, m.eta, Category.assoc, Category.assoc, m₂.eta]
      · rw [Category.assoc, h₂, Category.assoc, Over.w, ← Category.assoc, Over.w]
        simp

end
end

section

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo (IsTrans TIso)

private theorem pt_ext {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S S₁ T : Scheme.{0}} {s : S ⟶ Sp R} {s₁ : S₁ ⟶ Sp R} {f : S₁ ⟶ S} {o : GObj b N s} {o₁ : GObj b N s₁}
    (m : GObjMap o₁ o f) {t : T ⟶ S₁} (x y : Over.mk t ⟶ o₁.A) (h : x.left ≫ m.φ = y.left ≫ m.φ) : x = y := by
  letI := o.grp
  letI := o₁.grp
  apply GlobalTheory.SiegelPull.push_injective m.cart (Over.mk t)
  exact Over.OverMorphism.ext h

theorem UpperTheory.Gal.LocalSmoothExtension.transPull_of :
    HomEx → PolPull → TatePull → TransPull := by
  intro hHom hPol hTate p _ D G L R _ _ b N N' S S₁ s s₁ f hfs o' o'' o₁' o₁'' m' m'' h ψ hT
  obtain ⟨hψ, hact, ⟨ψ', d, hψ', hact', hc1, hc2, hd⟩, hpolc, hgeo⟩ := hT
  obtain ⟨c, hcp, hpol, hrest⟩ := hpolc
  letI := o'.grp
  letI := o''.grp
  letI := o₁'.grp
  letI := o₁''.grp
  obtain ⟨hlift, huniq, hpow⟩ := hHom D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m''
  obtain ⟨hlift', huniq', hpow'⟩ := hHom D.toG R b N' N S S₁ s s₁ f o'' o' o₁'' o₁' m'' m'
  have hu₁ := (hHom D.toG R b N' N' S S₁ s s₁ f o' o' o₁' o₁' m' m').2.1
  have hu₂ := (hHom D.toG R b N N S S₁ s s₁ f o'' o'' o₁'' o₁'' m'' m'').2.1
  obtain ⟨ψ₁, hψ₁, hcomm⟩ := hlift ψ hψ
  obtain ⟨ψ₁', hψ₁', hcomm'⟩ := hlift' ψ' hψ'
  refine ⟨ψ₁, hcomm, hψ₁, ?_, ⟨ψ₁', d, hψ₁', ?_, ?_, ?_, hd⟩,
    ⟨c, hcp, hPol D.toG R b N N' S S₁ s s₁ f o' o'' o₁' o₁'' m' m'' ψ ψ₁ hcomm c hpol, hrest⟩, ?_⟩
  · intro e
    apply huniq
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm, hcomm, reassoc_of% (m'.act e),
      m'.act e, m''.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact e]
  · intro e
    apply huniq'
    simp only [Over.comp_left, Category.assoc, reassoc_of% hcomm', hcomm', reassoc_of% (m''.act e),
      m''.act e, m'.act e]
    rw [← Over.comp_left, ← Over.comp_left, hact' e]
  · apply hu₁
    simp only [Over.comp_left, Category.assoc, hcomm', reassoc_of% hcomm, hpow d, ← hc1]
  · apply hu₂
    simp only [Over.comp_left, Category.assoc, hcomm, reassoc_of% hcomm', hpow' d, ← hc2]
  · intro k _ _ t β ht
    have htf : (t ≫ f) ≫ s = spMap β := by rw [Category.assoc, hfs, ht]
    obtain ⟨I', I'', h1, h2, h3⟩ := hgeo k (t ≫ f) β htf
    obtain ⟨I₁', k₁⟩ := hTate p D R b N' S S₁ s s₁ f o' o₁' m' k t I'
    obtain ⟨I₁'', k₂⟩ := hTate p D R b N S S₁ s s₁ f o'' o₁'' m'' k t I''
    have hu : ∀ {X : Scheme} (g : Sp k ⟶ X), Over.Hom.left (toUnit (Over.mk g)) = g := by
      intro X g
      simpa using Over.w (toUnit (Over.mk g))
    refine ⟨I₁', I₁'', fun y => ?_, fun y => ?_, fun n hn hp x y => ?_⟩
    · apply pt_ext m'
      simp only [Over.comp_left, Category.assoc, m'.eta, k₁, ← h1, hu]
    · apply pt_ext m''
      simp only [Over.comp_left, Category.assoc, m''.eta, k₂, ← h2, hu]
    · refine Iff.trans ?_ (h3 n hn hp x y)
      have e : Over.Hom.left (I₁'.ev n x ≫ ψ₁) ≫ m''.φ = Over.Hom.left (I'.ev n x ≫ ψ) := by
        rw [Over.comp_left, Category.assoc, hcomm, ← Category.assoc, k₁ n x, Over.comp_left]
      constructor
      · intro hxy
        apply Over.OverMorphism.ext
        rw [← e, hxy]
        exact k₂ n y
      · intro hxy
        apply pt_ext m''
        rw [e, hxy]
        exact (k₂ n y).symm
end

section

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.CertificateRingHomMap Module

private lemma common_eig {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (S : J → End ℂ M) (hS : ∀ i j, S i * S j = S j * S i) (θ : J → ℂ) (y : M) (hy : y ≠ 0)
    (hG : ∀ j, y ∈ (S j).maxGenEigenspace (θ j)) : ∃ x : M, x ≠ 0 ∧ ∀ j, S j x = θ j • x := by
  let G : Submodule ℂ M := ⨅ j, (S j).maxGenEigenspace (θ j)
  have hyG : y ∈ G := (Submodule.mem_iInf _).2 hG
  have hGne : G ≠ ⊥ := fun h => hy (by rw [h] at hyG; simpa using hyG)
  have hst : ∀ j, ∀ x ∈ G, S j x ∈ G := by
    intro j x hx
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (show Commute (S i) (S j) from hS i j) (θ i)
      ((Submodule.mem_iInf _).1 hx i)
  obtain ⟨v, hvG, hv0, hv⟩ := UpperTheory.V.LinAlg.simEig S hS _ G rfl hGne hst
  refine ⟨v, hv0, fun j => ?_⟩
  obtain ⟨c, hc⟩ := hv j
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hvG j)
  have h1 : (S j - θ j • (1 : End ℂ M)) v = (c - θ j) • v := by
    simp [hc, sub_smul]
  have hp : ∀ n : ℕ, ((S j - θ j • (1 : End ℂ M)) ^ n) v = (c - θ j) ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_apply_eq_comp, h1, map_smul, ih, smul_smul, pow_succ']
  rw [hp] at hk
  rcases smul_eq_zero.1 hk with h | h
  · have : c = θ j := sub_eq_zero.1 (by_contra fun h' => pow_ne_zero k h' h)
    rw [hc, this]
  · exact absurd h hv0

private lemma wop_restrict {M J : Type} [AddCommGroup M] [Module ℂ M] (U : Submodule ℂ M)
    (T : J → End ℂ M) (h : ∀ j, ∀ x ∈ U, T j x ∈ U) (s : List J →₀ ℂ) (x : U) :
    ((wop (fun j => (T j).restrict (h j)) s x : U) : M) = wop T s (x : M) := by
  have hw : ∀ (w : List J) (x : U),
      (((w.map fun j => (T j).restrict (h j)).prod x : U) : M) = (w.map T).prod (x : M) := by
    intro w
    induction w with
    | nil => intro x; simp
    | cons j w ih =>
      intro x
      simp only [List.map_cons, List.prod_cons, mul_apply_eq_comp, LinearMap.coe_restrict_apply, ih]
  unfold wop
  simp only [Finsupp.sum, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul, hw]

end UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.eigOf_of :
    UpperTheory.Gal.CertificateRingHomMap.ProjOne.{0} → EigOf := by
  open UpperTheory.Gal.CertificateRingHomMap Module in
  intro hP B J _ W _ _ _ T u θ hc
  let U : ∀ b, Submodule ℂ (W b) := fun b =>
    Submodule.span ℂ {x | ∃ (w : List J) (z : W b), x = ((w.map (T b)).prod * u b) z}
  have hst : ∀ b j, ∀ x ∈ U b, T b j x ∈ U b := by
    intro b j x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      exact Submodule.subset_span ⟨j :: w, z, by simp [mul_apply_eq_comp]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hcm : ∀ b j j', ∀ x ∈ U b, T b j (T b j' x) = T b j' (T b j x) := by
    intro b j j' x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨w, z, rfl⟩ := h
      have := LinearMap.congr_fun (hc b j j' w) z
      simpa [mul_apply_eq_comp] using this
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul a x _ hx => simp only [map_smul, hx]
  let S : ∀ b, J → End ℂ (U b) := fun b j => (T b j).restrict (hst b j)
  have hS : ∀ b j j', S b j * S b j' = S b j' * S b j := by
    intro b j j'
    ext ⟨x, hx⟩
    exact hcm b j j' x hx
  let T' : J → ∀ b, End ℂ (U b) := fun j b => S b j
  cases nonempty_fintype B
  obtain ⟨s, h1, -, h3⟩ := hP ℂ (∀ b, End ℂ (U b)) J T' (fun i j => funext fun b => hS b i j) θ
  refine ⟨s, h1, fun b hne => ?_⟩
  have hev : (wop T' s) b = wop (S b) s := map_wop (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) T' s
  obtain ⟨z, hz⟩ : ∃ z, (wop (T b) s * u b) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  have hu : u b z ∈ U b := Submodule.subset_span ⟨[], z, by simp⟩
  have hcoe : ((wop (S b) s ⟨u b z, hu⟩ : U b) : W b) = wop (T b) s (u b z) :=
    wop_restrict (U b) (T b) (hst b) s ⟨u b z, hu⟩
  have hy : wop (S b) s ⟨u b z, hu⟩ ≠ 0 := by
    intro h
    apply hz
    rw [mul_apply_eq_comp, ← hcoe, h]
    rfl
  have hyG : ∀ j, wop (S b) s ⟨u b z, hu⟩ ∈ (S b j).maxGenEigenspace (θ j) := by
    intro j
    obtain ⟨N, hN⟩ := h3 j
    have hN' := congrArg (Pi.evalAlgHom ℂ (fun b => End ℂ (U b)) b) hN
    rw [map_mul, map_pow, map_sub, AlgHom.commutes, map_zero] at hN'
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨N, ?_⟩
    have h2 : (S b j - θ j • (1 : End ℂ (U b))) ^ N * wop (S b) s = 0 := by
      rw [← hev, Algebra.algebraMap_eq_smul_one] at *
      exact hN'
    have := LinearMap.congr_fun h2 ⟨u b z, hu⟩
    simpa [mul_apply_eq_comp] using this
  obtain ⟨x, hx0, hx⟩ := common_eig (S b) (hS b) θ _ hy hyG
  refine ⟨(x : W b), fun h => hx0 (Subtype.ext h), fun j => ?_⟩
  exact congrArg Subtype.val (hx j)
end

section

open UpperTheory.Gal.LocalSmoothExtension

open Polynomial in
private theorem rev_lin (r : ℂ) (hr : r ≠ 0) :
    (X - C r : ℂ[X]).reverse = C (-r) * (X - C r⁻¹) := by
  have h1 : (C (-r) * (X - C r⁻¹) : ℂ[X]) = 1 - C r * X := by
    rw [mul_sub, ← C_mul]
    simp [hr]
    ring
  rw [h1]
  ext n
  rw [coeff_reverse, natDegree_X_sub_C]
  rcases n with _ | _ | n
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C]
  · rw [revAt_le (by norm_num)]
    simp [coeff_X, coeff_C, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]
    simp [coeff_X, coeff_one, coeff_C]

open Polynomial in
private theorem rev_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, z ≠ 0) :
    ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse.roots = s.map (fun z => z⁻¹) := by
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero, ← C_1, reverse_C, roots_C, Multiset.map_zero]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self a s)
    have ih' := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have hm : ((s.map (fun a => X - C a)).prod : ℂ[X]) ≠ 0 :=
      (monic_multiset_prod_of_monic s _ fun a _ => monic_X_sub_C a).ne_zero
    have hm' : ((s.map (fun a => X - C a)).prod : ℂ[X]).reverse ≠ 0 := by
      simpa [reverse_eq_zero] using hm
    have hl : (C (-a) * (X - C a⁻¹) : ℂ[X]) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr ha)) (X_sub_C_ne_zero _)
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, rev_lin a ha,
      roots_mul (mul_ne_zero hl hm'), roots_C_mul _ (neg_ne_zero.mpr ha), roots_X_sub_C, ih',
      Multiset.map_cons, Multiset.singleton_add]

open Polynomial in
private theorem rev_roots (Q : ℂ[X]) (h0 : Q.coeff 0 ≠ 0) :
    Q.reverse.roots = Q.roots.map (fun z => z⁻¹) := by
  have hQ : Q ≠ 0 := fun h => h0 (by simp [h])
  have hc : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hf := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hz : ∀ z ∈ Q.roots, z ≠ 0 := by
    rintro z hz rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact (mem_roots hQ).mp hz)
  have hl : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  conv_lhs => rw [← hf]
  rw [reverse_mul_of_domain, reverse_C, roots_C_mul _ hl, rev_prod _ hz]

open Polynomial in
theorem UpperTheory.Gal.LocalSmoothExtension.invRoots_of :
    InvRoots := by
  intro F _ _ P h0 τ
  have hτ : τ (P.coeff 0) ≠ 0 := by simpa using h0
  have hmap : (P.map τ).coeff 0 ≠ 0 := by simpa [coeff_map] using h0
  have hrev : (P.reverse).map τ = (P.map τ).reverse := by
    rw [reverse, reverse, natDegree_map, reflect_map]
  have hinv : (invPol P).map τ = C (τ (P.coeff 0))⁻¹ * (P.map τ).reverse := by
    rw [invPol, Polynomial.map_mul, map_C, hrev, map_inv₀]
  simp only [UpperTheory.Gal.W2.rts]
  rw [hinv, roots_C_mul _ (inv_ne_zero hτ), rev_roots _ hmap]
end

section

open UpperTheory.Gal.LocalSmoothExtension

private theorem semi_symm {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) : IsSemi σ.symm e.symm := by
  intro c y
  apply e.injective
  rw [h]
  simp

private theorem exists_basis {σ : ℂ ≃+* ℂ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {e : V ≃+ V'} (h : IsSemi σ e) {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) :
    ∃ b' : Module.Basis ι ℂ V', ∀ y i, b'.repr y i = σ (b.repr (e.symm y) i) := by
  refine ⟨Module.Basis.ofRepr
    { toFun := fun y => Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))
      invFun := fun f => e (b.repr.symm (Finsupp.mapRange σ.symm (map_zero _) f))
      map_add' := fun x y => by
        ext i
        simp
      map_smul' := fun c y => by
        ext i
        have hs := semi_symm h c y
        simp [hs]
      left_inv := fun y => by
        have hr : Finsupp.mapRange σ.symm (map_zero _)
            (Finsupp.mapRange σ (map_zero σ) (b.repr (e.symm y))) = b.repr (e.symm y) := by
          ext i
          simp
        simp only [hr, LinearEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
      right_inv := fun f => by
        ext i
        simp }, ?_⟩
  intro y i
  rfl

theorem UpperTheory.Gal.LocalSmoothExtension.traceSemi_of :
    TraceSemi := by
  intro σ V V' _ _ _ _ e h T T' hT
  classical
  by_cases H : ∃ s : Finset V, Nonempty (Module.Basis s ℂ V)
  · obtain ⟨s, ⟨b⟩⟩ := H
    obtain ⟨b', hb'⟩ := exists_basis h b
    have hbj : ∀ j, b' j = e (b j) := by
      intro j
      apply b'.repr.injective
      rw [b'.repr_self]
      ext k
      rw [hb', AddEquiv.symm_apply_apply, b.repr_self]
      by_cases hjk : j = k
      · subst hjk
        simp
      · simp [Finsupp.single_apply, hjk]

    rw [LinearMap.trace_eq_matrix_trace ℂ b, LinearMap.trace_eq_matrix_trace ℂ b', Matrix.trace,
    Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, hbj, hb', ← hT,
      AddEquiv.symm_apply_apply]
  · have H' : ¬ ∃ t : Finset V', Nonempty (Module.Basis t ℂ V') := by
      rintro ⟨t, ⟨c⟩⟩
      obtain ⟨c', -⟩ := exists_basis (semi_symm h) c
      exact H ⟨_, ⟨c'.reindexFinsetRange⟩⟩
    simp only [LinearMap.trace, dif_neg H, dif_neg H', LinearMap.zero_apply, map_zero]
end

section

open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.cntFn_of :
    CntFn := by
  intro Γ _ K K' M h hKK' hMn hidx hconj
  have hrep : ∀ (c m : K'), m ∈ M.subgroupOf K' → ∀ y : Γ,
      (h * ((c * m : K') : Γ) * y ∈ K ↔ h * (c : Γ) * y ∈ K) := by
    intro c m hm y
    have hm' : (m : Γ) ∈ M := Subgroup.mem_subgroupOf.mp hm
    have key : h * ((c * m : K') : Γ) * y = (h * (c : Γ) * m * (h * c)⁻¹) * (h * c * y) := by
      push_cast
      group
    rw [key]
    exact Subgroup.mul_mem_cancel_left K (hconj c c.2 m hm')
  have hnz : ∀ y : Γ, cntFn K K' M h y ≠ 0 →
      ∃ q : K' ⧸ M.subgroupOf K', h * ((Quotient.out q : K') : Γ) * y ∈ K := by
    intro y hy
    unfold cntFn at hy
    obtain ⟨⟨q, hq⟩⟩ := (Nat.card_ne_zero.mp (Nat.cast_ne_zero.mp hy)).1
    exact ⟨q, hq⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k hk y
    constructor
    · haveI : (M.subgroupOf K').Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using hMn g g.2 n hn⟩
      unfold cntFn
      congr 1
      refine Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.mulRight (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K'))) ?_)
      intro q
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (M.subgroupOf K') (Quotient.out q * ⟨k, hKK' hk⟩)
      have hq : q * (((⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K')) =
          ((Quotient.out q * ⟨k, hKK' hk⟩ : K') : K' ⧸ M.subgroupOf K') := by
        rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
      simp only [Equiv.coe_mulRight]
      rw [hq, hm, hrep _ _ m.2]
      simp only [Subgroup.coe_mul, mul_assoc]
    · unfold cntFn
      simp only [← mul_assoc, Subgroup.mul_mem_cancel_right K hk]
  · intro y hy
    obtain ⟨q, hq⟩ := hnz y hy
    refine ⟨(h * ((Quotient.out q : K') : Γ) * y)⁻¹, K.inv_mem hq, _, (Quotient.out q).2, ?_⟩
    group
  · haveI : (M.subgroupOf K').FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
    refine (Set.finite_range (fun q : K' ⧸ M.subgroupOf K' =>
      ((((Quotient.out q : K') : Γ)⁻¹ * h⁻¹ : Γ) : Γ ⧸ K))).subset ?_
    intro y hy
    obtain ⟨q, hq⟩ := hnz _ hy
    refine ⟨q, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' y]
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hq
end

section

open UpperTheory.Gal.LocalSmoothExtension
open CategoryTheory

theorem UpperTheory.Gal.LocalSmoothExtension.powComp_of :
    PowComp := by
  intro S₁ S₂ S₃ A₁ A₂ A₃ f g e φ χ ω h₁ h₂ h₃ hfg hφχ k
  subst hfg
  subst hφχ
  apply GlobalTheory.KS.PowPB.pow_left_hom_ext
  · rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_w, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_w,
      GlobalTheory.KS.PowPB.powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, GlobalTheory.KS.PowPB.powMap_pr, ← Category.assoc, GlobalTheory.KS.PowPB.powMap_pr,
      GlobalTheory.KS.PowPB.powMap_pr, Category.assoc]
end
