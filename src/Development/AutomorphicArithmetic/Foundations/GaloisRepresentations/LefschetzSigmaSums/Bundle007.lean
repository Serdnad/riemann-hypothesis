module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.G3 (bcMap bcMap_fst bcMap_snd)
open UpperTheory.Gal.Int.Geo (KS Lv)

private theorem level_isPullback {S S' B B' Z : Scheme.{0}} {A : Over S} {A' : Over S'} {s : S ⟶ B'} {s' : S' ⟶ B}
    {f : S' ⟶ S} {g : B ⟶ B'} {φ : A'.left ⟶ A.left} (hφ : φ ≫ A.hom = A'.hom ≫ f)
    (H : IsPullback φ A'.hom A.hom f) (hf : IsPullback f s' s g) (k : ℕ) {q : Z ⟶ B'}
    (e : Z ≅ (GlobalTheory.KS.pow A k).left) (he : e.hom ≫ (GlobalTheory.KS.pow A k).hom ≫ s = q) :
    IsPullback (GlobalTheory.KS.powMap f φ hφ k ≫ e.inv) ((GlobalTheory.KS.pow A' k).hom ≫ s') q g := by
  have P := (GlobalTheory.KS.PowPB.powMap_isPullback S S' A A' f φ hφ H k).paste_vert hf
  have Q : IsPullback e.inv ((GlobalTheory.KS.pow A k).hom ≫ s) q (𝟙 B') := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [← he, Category.comp_id, Iso.inv_hom_id_assoc]
  have R := P.paste_horiz Q
  rw [Category.comp_id] at R
  exact R

private theorem pow_square (pc : PowComp) {S₁ S₂ S₁' S₂' : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {f₁ : S₁' ⟶ S₁} {f₂ : S₂' ⟶ S₂} {π : S₂ ⟶ S₁} {π' : S₂' ⟶ S₁'} {φ₁ : A₁'.left ⟶ A₁.left}
    {φ₂ : A₂'.left ⟶ A₂.left} {χ : A₂.left ⟶ A₁.left} {χ' : A₂'.left ⟶ A₁'.left}
    (h₁ : φ₁ ≫ A₁.hom = A₁'.hom ≫ f₁) (h₂ : φ₂ ≫ A₂.hom = A₂'.hom ≫ f₂)
    (hχ : χ ≫ A₁.hom = A₂.hom ≫ π) (hχ' : χ' ≫ A₁'.hom = A₂'.hom ≫ π')
    (hπ : π' ≫ f₁ = f₂ ≫ π) (hc : χ' ≫ φ₁ = φ₂ ≫ χ) (k : ℕ) :
    GlobalTheory.KS.powMap π' χ' hχ' k ≫ GlobalTheory.KS.powMap f₁ φ₁ h₁ k = GlobalTheory.KS.powMap f₂ φ₂ h₂ k ≫ GlobalTheory.KS.powMap π χ hχ k := by
  have h₃ : (φ₂ ≫ χ) ≫ A₁.hom = A₂'.hom ≫ (f₂ ≫ π) := by
    rw [Category.assoc, hχ, ← Category.assoc, h₂, Category.assoc]
  rw [pc _ _ _ A₂' A₁' A₁ π' f₁ (f₂ ≫ π) χ' φ₁ (φ₂ ≫ χ) hχ' h₁ h₃ hπ hc k,
    pc _ _ _ A₂' A₂ A₁ f₂ π (f₂ ≫ π) φ₂ χ (φ₂ ≫ χ) h₂ hχ h₃ rfl rfl k]

private theorem level_tr {S₁ S₂ S₁' S₂' B B' Z₁ Z₂ : Scheme.{0}} {A₁ : Over S₁} {A₂ : Over S₂} {A₁' : Over S₁'}
    {A₂' : Over S₂'} {q₁ : Z₁ ⟶ B'} {q₂ : Z₂ ⟶ B'} {g : B ⟶ B'} {k : ℕ} {s₁' : S₁' ⟶ B} {s₂' : S₂' ⟶ B}
    {Φ₁ : (GlobalTheory.KS.pow A₁' k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Φ₂ : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₂ k).left}
    {Ψ : (GlobalTheory.KS.pow A₂ k).left ⟶ (GlobalTheory.KS.pow A₁ k).left} {Ψ' : (GlobalTheory.KS.pow A₂' k).left ⟶ (GlobalTheory.KS.pow A₁' k).left}
    {π' : S₂' ⟶ S₁'} (hΨ' : Ψ' ≫ (GlobalTheory.KS.pow A₁' k).hom = (GlobalTheory.KS.pow A₂' k).hom ≫ π') (hs : π' ≫ s₁' = s₂')
    (hsq : Ψ' ≫ Φ₁ = Φ₂ ≫ Ψ) (e₁ : Z₁ ≅ (GlobalTheory.KS.pow A₁ k).left) (e₂ : Z₂ ≅ (GlobalTheory.KS.pow A₂ k).left)
    (t : Z₂ ⟶ Z₁) (ht : t ≫ q₁ = q₂) (he : t ≫ e₁.hom = e₂.hom ≫ Ψ)
    (P₁ : IsPullback (Φ₁ ≫ e₁.inv) ((GlobalTheory.KS.pow A₁' k).hom ≫ s₁') q₁ g)
    (P₂ : IsPullback (Φ₂ ≫ e₂.inv) ((GlobalTheory.KS.pow A₂' k).hom ≫ s₂') q₂ g) :
    bcMap g t ht ≫ P₁.isoPullback.symm.hom = P₂.isoPullback.symm.hom ≫ Ψ' := by
  have hΨ : Ψ ≫ e₁.inv = e₂.inv ≫ t := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply P₁.hom_ext
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst, bcMap_fst]
    rw [reassoc_of% hsq, hΨ, ← Category.assoc Φ₂ e₂.inv t, IsPullback.isoPullback_inv_fst_assoc]
  · simp only [Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_snd, bcMap_snd]
    rw [reassoc_of% hΨ', hs, IsPullback.isoPullback_inv_snd]

theorem UpperTheory.Gal.LocalSmoothExtension.kSBc_of :
    ModelBc → LegBc → PowComp → KSBc := by
  intro hmod hleg pc p _ D G L R _ _ gb k T τ gb' hρ ht
  have ht' : ∀ i, gb'.t i = τ.comp (gb.t i) := fun i => RingHom.ext fun c => ht i c
  have hM := fun N : Lv p => hmod D.toG R ℂ τ gb gb' hρ ht' (↑N) (T.M N)
  choose M' f hpb hm using hM
  let m := fun N => (hm N).some
  have hφ : ∀ N, (m N).φ ≫ (T.M N).univ.A.hom = (M' N).univ.A.hom ≫ f N := fun N => (m N).cart.1.w
  have P : ∀ N, IsPullback (GlobalTheory.KS.powMap (f N) (m N).φ (hφ N) k ≫ (T.e N).inv)
      ((GlobalTheory.KS.pow (M' N).univ.A k).hom ≫ (M' N).s) (T.X.q (T.lev N)) (Spec.map (CommRingCat.ofHom τ)) :=
    fun N => level_isPullback (hφ N) (m N).cart.1 (hpb N) k (T.e N) (T.e_q N)
  refine ⟨UpperTheory.Gal.Int.Geo.KS.mk (towerBc T.X (Spec.map (CommRingCat.ofHom τ))) T.lev T.K_eq T.Δ_eq M'
    (fun N => (P N).isoPullback.symm) ?_ ?_, rfl, HEq.rfl⟩
  · intro N
    exact (P N).isoPullback_inv_snd
  · intro N' N h a b
    obtain ⟨π₀, o₀, ψ₀, φ₀, hw₀, hs₀, htr₀, he₀⟩ := T.tr_eq N' N h a b
    obtain ⟨π₁, o₁, ψ₁, φ₁, hs₁, htr₁, hπ, hc⟩ := hleg p D G L R ℂ τ gb gb' hρ ht' N N' (T.M N) (T.M N')
      (M' N) (M' N') (f N) (f N') (hpb N) (hpb N') (m N) (m N') h π₀ o₀ ψ₀ φ₀ hs₀ htr₀
    have hw₁ : (Over.Hom.left ψ₁ ≫ φ₁.φ) ≫ (M' N).univ.A.hom = (M' N').univ.A.hom ≫ π₁ := by
      rw [Category.assoc, φ₁.cart.1.w, ← Category.assoc, Over.w]
    refine ⟨π₁, o₁, ψ₁, φ₁, hw₁, hs₁, htr₁, ?_⟩
    exact level_tr (GlobalTheory.KS.PowPB.powMap_w π₁ _ hw₁ k) hs₁
      (pow_square pc (hφ N) (hφ N') hw₀ hw₁ hπ hc k) (T.e N) (T.e N') _ (T.X.tr_q _ _ h a b) he₀ (P N) (P N')
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open scoped Classical

namespace UpperTheory.Gal.LocalSmoothExtension

theorem geoStep_of :
    HolomorphicLefschetzFormula → KSProj → FixK → LefSum → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.HopOp.{0} → UpperTheory.Gal.G3.OpTr.{0} → GeoStep := by
  intro W1 KSP FK LS HG HT HO OT p _ D G L sc gb std i₀ v hv k T N d hd h hΔ hreg α hα
  obtain ⟨m, hm1, -, hm3⟩ := T.X.deep (T.lev N) {(T.lev N, h)}
  obtain ⟨N₁, rfl⟩ := T.lev.surjective m
  obtain ⟨N', hdvd, hle⟩ : ∃ N' : Lv p, N.1 ∣ N'.1 ∧ T.X.K (T.lev N') ≤ T.X.K (T.lev N₁) := by
    refine ⟨⟨N.1 * N₁.1, le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N₁.2.1; omega)),
      Nat.coprime_mul_iff_left.2 ⟨N.2.2, N₁.2.2⟩⟩, Dvd.intro _ rfl, ?_⟩
    rw [T.K_eq, T.K_eq]
    exact UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro_left _ rfl)
  have a₀ : T.X.admitted (T.lev N') (T.lev N) 1 := T.X.isAdmissibleIntegralBasisChange_one (hle.trans hm1)
  have b₀ : T.X.admitted (T.lev N') (T.lev N) h := ⟨hΔ, fun u hu => hm3 (T.lev N, h) (by simp) u (hle hu)⟩
  obtain ⟨hcx, hfin, het, F, A, hF, hA, hsum⟩ := FK p D G L sc gb std i₀ v hv k T N' N hdvd d hd h a₀ b₀ hreg α hα
  refine ⟨hcx, fun y => ?_⟩
  haveI := T.X.fin (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := T.X.etale (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := hd
  have hq1 : T.X.tr _ _ 1 a₀.1 a₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hqh : T.X.tr _ _ h b₀.1 b₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hop := fun a b => HO T.X (hodge ℂ a b) (HG ℂ a b) (T.lev N') (T.lev N) h a₀ b₀
  have hW := W1 _ (qAt T N) d (KSP p D G L sc gb k T N).1 _ (qAt T N') (T.X.tr _ _ 1 a₀.1 a₀.2) (leg T N' N h b₀ α)
    hq1 (leg_q T N' N h b₀ α) hfin het F hF A hA
  have hne : (L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) ≠ 0 := by
    have := (hop 0 0).1
    rwa [T.K_eq N', T.K_eq N] at this
  have hc : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have key : ∀ a b, hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
        (hodgeTrace hq1 a b ∘ₗ hodgePull (leg_q T N' N h b₀ α) a b) := by
    intro a b
    have hIs := (hop a b).2
    rw [T.K_eq N', T.K_eq N] at hIs
    have e := (OT (hodge ℂ a b) (HG ℂ a b) (qAt T N) (qAt T N') (qAt T N) _ _ hq1 hqh (hodgeTrace hq1 a b)
      (HT ℂ a b _ _ _ hq1) _).1 hIs
    have e2 : hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
        (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
          (hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b) := by
      have e' : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) • hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
          hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b := e
      rw [← e', smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e2]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [hodgePull_comp (al_q T N α) hqh (leg_q T N' N h b₀ α) a b x]
    rfl
  have hinner : ∀ a, ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
        ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det := by
    intro a
    rw [← (hW a).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [key a b, map_smul, smul_eq_mul]
    ring
  have hfinal : altTr (qAt T N) d (fun a b => hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) y =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, UpperTheory.Gal.W2.lefTerm (A x) y := by
    unfold altTr
    calc _ = ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
              ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) :=
          Finset.sum_congr rfl fun a _ => by rw [hinner a]
      _ = (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun x _ => LS d (A x) y
  rw [hfinal, hsum y, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end UpperTheory.Gal.LocalSmoothExtension
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.HodgeCoh

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem trace_comb {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ} {A : Type*}
    (u : Fin m → Module.End ℂ M) (c : Fin m → ℂ) (w : A →₀ ℂ) (e : A → Module.End ℂ M) :
    LinearMap.trace ℂ M ((∑ i, c i • u i) ∘ₗ w.sum fun α r => r • e α) =
      ∑ i, c i * w.sum fun α r => r * LinearMap.trace ℂ M (u i ∘ₗ e α) := by

  simp only [Finsupp.sum, ← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
  mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
  ring

private theorem sum_rearrange {m : ℕ} {A : Type*} (R : Finset ℕ) (S : Finset A) (c : Fin m → ℂ) (w : A → ℂ)
    (x z : ℕ → ℂ) (t : Fin m → A → ℕ → ℕ → ℂ) :
    ∑ a ∈ R, x a * ∑ b ∈ R, z b * ∑ i, c i * ∑ α ∈ S, w α * t i α a b =
      ∑ i, c i * ∑ α ∈ S, w α * ∑ a ∈ R, x a * ∑ b ∈ R, z b * t i α a b := by
  simp only [Finset.mul_sum]
  calc _ = ∑ a ∈ R, ∑ i, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) := Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ α ∈ S, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ α ∈ S, ∑ a ∈ R, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

private theorem alt_family {M : ℕ → ℕ → Type*} [∀ a b, AddCommGroup (M a b)] [∀ a b, Module ℂ (M a b)]
    (d m : ℕ) {A : Type*} (u : Fin m → ∀ a b : ℕ, Module.End ℂ (M a b)) (c : Fin m → ℂ) (w : A →₀ ℂ)
    (e : A → ∀ a b : ℕ, Module.End ℂ (M a b)) (y : ℂ) :
    ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
        LinearMap.trace ℂ (M a b) ((∑ i, c i • u i a b) ∘ₗ w.sum fun α r => r • e α a b) =
      ∑ i, c i * w.sum fun α r => r * ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b) := by
  simp only [trace_comb]
  simp only [Finsupp.sum]
  exact sum_rearrange (Finset.range (d + 1)) w.support c (fun α => w α) (fun a => (-y) ^ a) (fun b => (-1 : ℂ) ^ b)
    fun i α a b => LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b)

theorem altLin_of : AltLin := fun Z s d m A u c w e y =>
  alt_family (M := fun a b => hodgeH s a b) d m u c w e y

end UpperTheory.Gal.LocalSmoothExtension
end
end

section

open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Gal.Int.Geo in
theorem UpperTheory.Gal.LocalSmoothExtension.kSHodge_of :
    HodgeEig → KSBc → SpecConj → MemOp → FnDecomp → OccOf → UpperTheory.Gal.Int.Geo.KSHodge := by
  intro hE hB hS hM hF hO p _ D G L sc lam anti
  obtain ⟨k, hk⟩ := hE p D G L sc lam anti
  refine ⟨k, ?_⟩
  intro R _ _ gb T N J g θ f hf hs τ hρ ht σ i₀ h hh i
  let gb' : GBase D.toG ℂ :=
    { ρ := D.ρc
      ρ_root := D.toG.ρc_root
      t := fun i => (D.toG.tau i).comp (algebraMap _ _)
      t_ω := fun i => D.toG.tau_ω i
      comax := fun i j hij => by
        have ha : D.toG.a = 1 := sc.a1
        exact absurd (Fin.ext (by have := i.2; have := j.2; omega)) hij }
  have hstd : StdC D gb' := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨⟨X', lev', c1, c2, c3, c4, c5, c6⟩, hX, hl⟩ :=
    hB p D G L R gb k T τ gb' hρ.symm (fun i c => (ht i c).symm)
  dsimp only at hX
  subst hX
  cases hl
  have e : (fun (j : J) (y : G.GAf) => σ ((g j).fn y)) = fun j => (g j).fn := by
    funext j y
    exact map_natCast σ _
  have h1 := hS σ p D G L lam (L.KN N.1) J (fun j => (g j).fn) θ f hs
  rw [e] at h1
  have hfn : T.X.IsFn (T.lev N) f := by
    refine (hF _ _ T.X (T.lev N) f).2 ?_ ?_
    · rw [T.K_eq]; exact hf.1
    · intro y hy
      exact (T.Δ_eq _).2 (hf.2 y hy)
  have hfn' : T.X.IsFn (T.lev N) fun y => σ (f y) := by
    obtain ⟨a1, a2, a3⟩ := hfn
    refine ⟨fun k hk y => ⟨?_, ?_⟩, fun y hy => a2 y ?_, a3.subset fun y hy => ?_⟩
    · show σ _ = σ _
      rw [(a1 k hk y).1]
    · show σ _ = σ _
      rw [(a1 k hk y).2]
    · exact fun h0 => hy (by show σ (f y) = 0; rw [h0, map_zero])
    · exact fun h0 => hy (by show σ (f y.out) = 0; rw [h0, map_zero])
  obtain ⟨b, x, hx, hx'⟩ := hk gb' hstd ⟨_, T.lev, c1, c2, c3, c4, c5, c6⟩ N σ i₀ h hh J (fun j => (g j).fn)
    (fun j => σ (θ j)) (fun y => σ (f y)) (fun j => (hM p D G L R gb k T N J g j).1) hfn' h1 i
  exact hO p D G L R gb k T N J g τ _ (h i) b x hx hx'
end

section

open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.HodgeCoh UpperTheory.Gal.CertificateRingHomMap in
theorem UpperTheory.Gal.LocalSmoothExtension.hodgeEig_of :
    HodgeTr → KSProj → HodgeFin → UnifBound → HExpInj → CoeffOcc → EigOf → HopWord → UpperTheory.Gal.G3.HodgeGood → HodgeEig := by
  intro hTr hProj hFin hUnif hInj hCo hEig hWord hGood
  intro p _ D G L hSc lam hlam
  classical
  let κ : ((D.F →+* ℂ) → Fin G.n → ℕ) → Fin D.a → (Fin G.n → ℕ) → ℕ := fun lam' i₀ h =>
    if H : IsHExp (D.tau i₀) (epsOf D) lam' h then (hTr p D G L lam' i₀ h H).choose else 0
  obtain ⟨k, hkB⟩ := hUnif D.F G.n (Fin D.a) D.tau (epsOf D) lam κ
  refine ⟨k, ?_⟩
  intro gb hgb T N σ i₀ h hH J ψ θ f hψ hf hS i
  have hκ : (hTr p D G L (conjWt σ lam) i₀ h hH).choose ≤ k := by
    have := hkB σ i₀ h hH
    simpa only [κ, dif_pos hH] using this
  obtain ⟨c, hc⟩ := (hTr p D G L (conjWt σ lam) i₀ h hH).choose_spec k hκ
  obtain ⟨hproj, d, hd⟩ := hProj p D G L hSc gb k T N
  have hcT := hc hSc gb hgb T N d hd
  have hG : ∀ a b, (UpperTheory.Gal.G3.hodge ℂ a b).Good := fun a b => hGood ℂ a b
  haveI hFD : ∀ b : Fin (d + 1), FiniteDimensional ℂ (hodgeH (qAt T N) (h i) b.1) :=
    fun b => hFin _ _ d hd hproj _ _
  have hWd : ∀ (a b : ℕ) (w : List J), T.X.IsFn (T.lev N) (wordFn (L.KN N.1) ψ w f) ∧
      hk T N (wordFn (L.KN N.1) ψ w f) a b = (w.map fun j => hk T N (ψ j) a b).prod * hk T N f a b := by
    intro a b w
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).1 w
    rw [T.K_eq] at this
    exact this
  have hPoly : ∀ (a b : ℕ) (s : List J →₀ ℂ), T.X.IsFn (T.lev N) (polyFn (L.KN N.1) ψ s f) ∧
      hk T N (polyFn (L.KN N.1) ψ s f) a b = wop (fun j => hk T N (ψ j) a b) s * hk T N f a b := by
    intro a b s
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).2 s
    rw [T.K_eq] at this
    exact this
  obtain ⟨hcomm, V, _, _, _, ξ, hξ, hspec⟩ := hS
  have hcm : ∀ (b : Fin (d + 1)) (j j' : J) (w : List J),
      hk T N (ψ j) (h i) b.1 * hk T N (ψ j') (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 =
        hk T N (ψ j') (h i) b.1 * hk T N (ψ j) (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 := by
    intro b j j' w
    have h1 := (hWd (h i) b.1 (j :: j' :: w)).2
    have h2 := (hWd (h i) b.1 (j' :: j :: w)).2
    rw [hcomm j j' w, h2] at h1
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using h1.symm
  obtain ⟨s, hs1, hs⟩ := hEig (Fin (d + 1)) J (fun b => hodgeH (qAt T N) (h i) b.1)
    (fun b j => hk T N (ψ j) (h i) b.1) (fun b => hk T N f (h i) b.1) θ hcm
  have hne : wop θ s ≠ 0 := by rw [hs1]; exact one_ne_zero
  obtain ⟨a, hgoodF, hdT⟩ := hspec s hne
  have hFfn := (hPoly 0 0 (wmul a s)).1
  have hy := fun y => hcT V ξ hξ _ hFfn hgoodF y
  have hocc := hCo d G.n
    (fun a' => ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
      LinearMap.trace ℂ _ (hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) a' b ∘ₗ cutD T N c a' b)) _ h
    (hInj D.F G.n (D.tau i₀) (epsOf D) (conjWt σ lam) h (fun τ => hlam _) hH) hdT hy i
  obtain ⟨b, hb, hb0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hocc
  have hne0 : hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) (h i) b ≠ 0 := by
    intro e
    apply hb0
    rw [e, LinearMap.zero_comp, map_zero, mul_zero]
  rw [(hPoly _ _ _).2, wop_wmul, mul_assoc] at hne0
  have hu : wop (fun j => hk T N (ψ j) (h i) b) s * hk T N f (h i) b ≠ 0 :=
    fun e => hne0 (by rw [e, mul_zero])
  obtain ⟨x, hx0, hx⟩ := hs ⟨b, Finset.mem_range.1 hb⟩ hu
  exact ⟨b, x, hx0, hx⟩
end

section

open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
end

section

set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.LocalSmoothExtension

namespace UpperTheory.Gal.LocalSmoothExtension

open UpperTheory.Gal.G3 (Tower Th)

variable {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ] (X : Tower B Γ) (T : Th.{0} B ℂ)

private theorem hecke_zero (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ)) :
    X.hecke T j 0 = 0 := by
  have h := (hL X T hT j 0 0 0 hz hz).2
  simpa using h

private theorem hecke_sum (hL : UpperTheory.Gal.G3.HopLin.{0}) (hT : T.Good) (j : X.ι) (hz : X.IsFn j (0 : Γ → ℂ))
    (hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f'))
    (hsm : ∀ (c : ℂ) (f : Γ → ℂ), X.IsFn j f → X.IsFn j (c • f))
    {I : Type} (s : Finset I) (f : I → Γ → ℂ) (c : I → ℂ) (hf : ∀ i ∈ s, X.IsFn j (f i)) :
    X.IsFn j (∑ i ∈ s, c i • f i) ∧ X.hecke T j (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • X.hecke T j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using hz, by simpa using hecke_zero X T hL hT j hz⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h3 := hsm (c a) (f a) (hf a (Finset.mem_insert_self a s))
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hadd _ _ h3 h1, ?_⟩
    rw [(hL X T hT j _ _ 0 h3 h1).1, h2,
      (hL X T hT j (f a) (f a) (c a) (hf a (Finset.mem_insert_self a s)) (hf a (Finset.mem_insert_self a s))).2]

end UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.hopWord_of :
    UpperTheory.Gal.G3.FnRing → UpperTheory.Gal.G3.HopLin.{0} → UpperTheory.Gal.G3.HopMul.{0} → HopWord := by
  intro hR hL hM B Γ _ X T hT j
  obtain ⟨-, hz, hfg, hsm⟩ := hR X ℂ j
  have hadd : ∀ f f' : Γ → ℂ, X.IsFn j f → X.IsFn j f' → X.IsFn j (f + f') := fun f f' a b => (hfg f f' a b).1
  refine ⟨fun m f c hf => hecke_sum X T hL hT j hz hadd hsm Finset.univ f c fun i _ => hf i, ?_⟩
  intro J ψ f hψ hf
  have hw : ∀ w : List J, X.IsFn j (wordFn (X.K j) ψ w f) ∧
      X.hecke T j (wordFn (X.K j) ψ w f) = (w.map fun i => X.hecke T j (ψ i)).prod * X.hecke T j f := by
    intro w
    induction w with
    | nil => exact ⟨hf, by simp [wordFn]⟩
    | cons i w ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : wordFn (X.K j) ψ (i :: w) f = UpperTheory.Gal.G3.conv (X.K j) (ψ i) (wordFn (X.K j) ψ w f) := rfl
      rw [e]
      refine ⟨(hfg _ _ (hψ i) h1).2, ?_⟩
      rw [hM X T hT j _ _ (hψ i) h1, h2, List.map_cons, List.prod_cons, mul_assoc]
  refine ⟨hw, fun s => ?_⟩
  have hs := hecke_sum X T hL hT j hz hadd hsm s.support (fun w => wordFn (X.K j) ψ w f) s fun w _ => (hw w).1
  have e : polyFn (X.K j) ψ s f = ∑ w ∈ s.support, s w • wordFn (X.K j) ψ w f := rfl
  rw [e]
  refine ⟨hs.1, ?_⟩
  rw [hs.2]
  unfold UpperTheory.Gal.CertificateRingHomMap.wop Finsupp.sum
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [(hw w).2, smul_mul_assoc]

end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.Int.Geo (KS Lv Sc)

theorem UpperTheory.Gal.LocalSmoothExtension.kSProj_of :
    ZSm → ZPr → KSProj := by
  intro hSm hPr p _ D G L hSc gb k T N
  have hq : qAt T N = (T.e N).hom ≫ ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s) := (T.e_q N).symm
  rw [hq]
  constructor
  · obtain ⟨M, i, hi, hi'⟩ := hPr p D hSc.cpt gb N.1 N.2.1 N.2.2 (T.M N) k
    refine ⟨M, (T.e N).hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hi']
  · obtain ⟨d, hd⟩ := hSm D.toG gb N.1 N.2.1 (T.M N) k
    haveI := hd
    have h0 : SmoothOfRelativeDimension 0 (T.e N).hom := inferInstance
    have h2 := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := d) (T.e N).hom
      ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s)
    rw [zero_add] at h2
    exact ⟨d, h2⟩
end
